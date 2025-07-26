#include "PTeX/BackwardAnalysis_CT.h"

#include "X86.h"
#include "X86InstrInfo.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "PTeX/Util.h"
#include "PTeX/PTeXAnalysis.h"
#include "PTeX/PTeX.h"

#define DEBUG_TYPE "x86-ptex-bwd"

#define PTEX_DEBUG(...) LLVM_DEBUG(dbgs() << DEBUG_TYPE << ": "; __VA_ARGS__);

using namespace llvm;
using llvm::X86::BackwardAnalysis_CT;

void BackwardAnalysis_CT::init() {
  const PublicPhysRegs bot(TRI);
  const PublicPhysRegs top = X86::computeTop(MF);

  // Compute which blocks are reachable by exits using a mini data-flow pass.
  std::unordered_set<MachineBasicBlock *> ExitReachingBlocks;
  getExitReachingBlocks(MF, ExitReachingBlocks);

  for (MachineBasicBlock &MBB : MF) {
    In[&MBB] = top;

    // Conservatively initialize the pub-outs of exit blocks to the parent analysis' pub-outs.
    // We consider anything without a successor to be an exit block.
    if (MBB.succ_empty()) {
      Out[&MBB] = Parent.Out[&MBB];
    } else if (!ExitReachingBlocks.count(&MBB)) {
      Out[&MBB] = bot;
    } else {
      Out[&MBB] = top;
    }
  }

  // Initialize PubOps.
  for (MachineBasicBlock &MBB : MF)
    for (MachineInstr &MI : MBB)
      for (MachineOperand &MO : MI.operands())
        if (MO.isReg() && !MO.isUndef())
          PubOps.insert(&MO);
}

bool BackwardAnalysis_CT::block(MachineBasicBlock &MBB) {
  bool Changed = false;

  // Meet block pub-out with successor block pub-ins.
  for (MachineBasicBlock *SuccMBB : MBB.successors())
    Changed |= Out[&MBB].intersect(In[SuccMBB]);

  // Now, transfer across the block, *in reverse order*.
  PublicPhysRegs PubRegs = Out[&MBB];
  for (MachineInstr &MI : llvm::reverse(MBB))
    Changed |= instruction(MI, PubRegs);

  // Finally, update the pub-ins.
  // TODO: Make this a dedicated member function so we don't make these kinds of mistakes.
  PubRegs.addRegs(Parent.In[&MBB]);
  Changed |= In[&MBB].intersect(PubRegs);

  return Changed;
}

bool BackwardAnalysis_CT::backpropSafeForInst_sSNI(const MachineInstr &MI, const PublicPhysRegs &PubRegs_) const {
  // Is this a copy instruction?
  if (TII->isFullCopyInstr(MI)) {
    PTEX_DEBUG(dbgs() << __func__ << ": copy: " << MI);
    return true;
  }

  PublicPhysRegs PubRegs = PubRegs_;
  PubRegs.stepBackward(MI);

  // Special cases: MOVSX, MOVZX
  const StringRef OpName = TII->getName(MI.getOpcode());
  if (OpName.starts_with("MOV"))
    return true;

  const unsigned NumProtectedUses = llvm::count_if(MI.operands(), [&] (const MachineOperand &MO) -> bool {
    return MO.isReg() && MO.isUse() && !PubRegs.isPublic(MO.getReg());
  });

  if (MI.mayLoad()) {
    // If this is a memory intruction, then allow no protected inputs.
    if (NumProtectedUses > 0)
      return false;
  } else {
    // If this is a non-memory instruction, then allow exactly one
    // protected input.
    if (NumProtectedUses > 1) {
      PTEX_DEBUG(dbgs() << __func__ << ": cannot backpropagate because NumProtectedUses=" << NumProtectedUses << ": " << MI);
      return false;
    }
  }

  // TODO: Should perform exact check again?

  switch (MI.getOpcode()) {
#define MAKE_CASE(name) case X86::name:
#define STD_ARITH(base, X)                      \
    X(base##8rr)                                \
        X(base##8ri)                            \
        X(base##8rm)                            \
        X(base##8mr)                            \
        X(base##8mi)                            \
        X(base##16rr)                           \
        X(base##16rm)                           \
        X(base##16mr)                           \
        X(base##16ri8)                          \
        X(base##16ri)                           \
        X(base##16mi8)                          \
        X(base##16mi)                           \
        X(base##32rr)                           \
        X(base##32rm)                           \
        X(base##32mr)                           \
        X(base##32ri8)                          \
        X(base##32ri)                           \
        X(base##32mi8)                          \
        X(base##32mi)                           \
        X(base##64rr)                           \
        X(base##64rm)                           \
        X(base##64mr)                           \
        X(base##64ri8)                          \
        X(base##64ri32)                         \
        X(base##64mi8)                          \
        X(base##64mi32)

#define STD_UNOP_SZ(base, size, X)              \
    X(base##size##r)                            \
        X(base##size##m)

#define STD_UNOP(base, X)                        \
    STD_UNOP_SZ(base, 8, X)                      \
        STD_UNOP_SZ(base, 16, X)                 \
        STD_UNOP_SZ(base, 32, X)                 \
        STD_UNOP_SZ(base, 64, X)

  case X86::MOV64rm:
  case X86::MOV64rr:
  case X86::COPY:
    STD_ARITH(ADD, MAKE_CASE)
        STD_ARITH(SUB, MAKE_CASE)
        STD_ARITH(XOR, MAKE_CASE)
        STD_UNOP(NEG, MAKE_CASE)
        STD_UNOP(NOT, MAKE_CASE)
        STD_UNOP(INC, MAKE_CASE)
        STD_UNOP(DEC, MAKE_CASE)

        PTEX_DEBUG(dbgs() << "backpropagation safe for instruction: " << MI);
        return true;

  case X86::IMUL64r:
  case X86::IMUL64rr:
  case X86::IMUL32r:
  case X86::IMUL32rr:
  case X86::IMUL16r:
  case X86::IMUL8r:
  case X86::IMUL64rri8:
  case X86::IMUL32rri8:
    if (MI.getFlag(MI.NoSWrap) || MI.getFlag(MI.NoUWrap)) {
      PTEX_DEBUG(dbgs() << "backprop: safe to imul with nsw/nuw: " << MI);
      return true;
    } else {
      PTEX_DEBUG(dbgs() << "backprop: unsafe imul: " << MI);
      return false;
    }

  case X86::LEA64r:
  case X86::LEA32r:
  case X86::LEA16r:
    {
      const int MemIdx = X86::getMemRefBeginIdx(MI);
      const MachineOperand &Scale = MI.getOperand(MemIdx + X86::AddrScaleAmt);
      const MachineOperand &Index = MI.getOperand(MemIdx + X86::AddrIndexReg);
      if (NumProtectedUses == 0) {
        return true;
      } else if (Scale.getImm() != 1 && Index.isReg() && !PubRegs.isPublic(Index.getReg())) {
        PTEX_DEBUG(dbgs() << "backpropagation unsafe for LEA because scale != 1: " << MI);
        return false;
      } else {
        PTEX_DEBUG(dbgs() << "backpropagation safe for LEA: " << MI);
        return true;
      }
    }

  default:
    PTEX_DEBUG(dbgs() << "backpropagation unsafe for instruction: " << MI);
    return false;
  }
}

bool BackwardAnalysis_CT::backpropSafeForInst(const MachineInstr &MI, const PublicPhysRegs &PubRegs) const {
  switch (X86::getPTeXMode(*MI.getParent()->getParent())) {
  case sSNI:
    return backpropSafeForInst_sSNI(MI, PubRegs);

  default:
    report_fatal_error("unhandled analysis type in backpropSafeForInst");
  }
}

// Returns true if any of the instruction data operands are public.
// TODO: Separation between backpropSafe and dataDefsPublic right now is pointless.
// Combnie and specialize for each PTeX config.
bool BackwardAnalysis_CT::dataDefsPublic(const MachineInstr &MI, const PublicPhysRegs &PubRegs) const {
  if (!backpropSafeForInst(MI, PubRegs))
    return false;

  switch (X86::getPTeXMode(*MI.getParent()->getParent())) {
  case sSNI:
    // All non-flag outputs must already be public.
    {
      bool AnyDefPub = false;
      for (const MachineOperand &MO : MI.operands()) {
        if (MO.isReg() && MO.isDef() && MO.getReg() != X86::EFLAGS) {
          if (!PubRegs.isPublic(MO.getReg()))
            return false;
          AnyDefPub = true;
        }
      }
      return AnyDefPub;
    }

  default:
    llvm_unreachable("unexpected PTeX mode!");
  }
}

bool BackwardAnalysis_CT::instruction(MachineInstr &MI, PublicPhysRegs &PubRegs) {
  bool Changed = false;

  // Remove any private defs in PubOps.
  for (MachineOperand &MO : MI.operands())
    if (MO.isReg() && MO.isDef() && !MO.isUndef() && !PubRegs.isPublic(MO.getReg()))
      Changed |= erasePubOp(&MO);

  const bool DefsPublic = dataDefsPublic(MI, PubRegs) && !MI.isCall(); // TODO: isCall prob. redundant.
  if (DefsPublic)
    PTEX_DEBUG(dbgs() << "bwd: DefsPublic: " << MI);

  // 2. Step backward.
  PubRegs.stepBackward(MI);
  if (DefsPublic)
    for (MachineOperand &MO : MI.operands())
      if (MO.isReg() && MO.isUse() && !MO.isUndef())
        PubRegs.addReg(MO.getReg());

  // Remove private uses.
  for (MachineOperand &MO : MI.operands())
    if (MO.isReg() && MO.isUse() && !MO.isUndef() && !PubRegs.isPublic(MO.getReg()))
      Changed |= erasePubOp(&MO);

  return Changed;
}


bool BackwardAnalysis_CT::run() {
  init();

  bool Changed;
  do {
    Changed = false;

    for (MachineBasicBlock *MBB : llvm::post_order(&MF))
      Changed |= block(*MBB);

  } while (Changed);

  bool OverallChanged = false;
  for (MachineOperand *MO : PubOps) {
    if (!MO->isPublic()) {
      OverallChanged = true;
      MO->setIsPublic();
    }
  }

  return OverallChanged;
}

bool BackwardAnalysis_CT::erasePubOp(const MachineOperand *MO) {
  const bool Changed = PubOps.erase(const_cast<MachineOperand *>(MO));
  if (Changed) {
    PTEX_DEBUG(dbgs() << "removed pub op \"" << *MO << "\" of instruction: " << *MO->getParent());
  }
  return Changed;
}
