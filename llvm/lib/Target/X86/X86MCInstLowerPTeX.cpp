#include "X86MCInstLowerPTeX.h"
#include "PTeX/PTeX.h"
#include "PTeX/Util.h"
#include "MCTargetDesc/X86BaseInfo.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/CodeGen/MachineBasicBlock.h"
#include "llvm/CodeGen/MachineFunction.h"
#include "llvm/IR/Function.h"
#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/WithColor.h"
#include "llvm/IR/Instructions.h"
#include "llvm/CodeGen/TargetInstrInfo.h"

#define DEBUG_TYPE "x86-ptex"

using namespace llvm;

namespace llvm::X86 {

static cl::opt<bool> AllowUntyped {
  "x86-ptex-allow-untyped",
  cl::desc("Allow untyped instructions (issue warning, but don't abort)"),
  cl::init(false),
  cl::Hidden,
};

static bool shouldConsiderInstructionForPrefix(const MachineInstr &MI) {
  if (!EnablePTeX())
    return false;

  // PTEX-TODO: Need to unify.
  if (MI.isCall())
    return false;

  SmallVector<const MachineOperand *, 2> OutRegs;
  X86::getInstrDataOutputs(MI, OutRegs);

  if (!OutRegs.empty())
    return true;

  if (MI.mayLoad())
    return true;

  if (PrefixProtectedStores && MI.mayStore())
    return true;

  return false;
}

static void annotate(const MachineInstr *MI, MCInst& OutMI) {
  if (MI->getFlag(MachineInstr::AnnotatePointerLoad)) {
    OutMI.setFlags(OutMI.getFlags() | X86::IP_USE_DS);
  }

  if (getPTeXMode() == NCT) {
    // Mark everything with an output register public.
    if (llvm::any_of(MI->operands(), [] (const MachineOperand &MO) -> bool {
      return MO.isReg() && MO.isDef();
    })) {
      OutMI.setFlags(OutMI.getFlags() | X86::IP_TPE_PRIVM);
    }
  }
}

// PTEX-TODO: Rename function.
void X86MCInstLowerTPE(const MachineInstr *MI, MCInst& OutMI) {
  annotate(MI, OutMI);

  if (MI->getOpcode() == X86::POP64r && getPTeXMode() == X86::NCT)
    for (const MachineOperand &MO : MI->operands())
      if (MO.isReg() && MO.isDef() && !MO.isImplicit() && !MO.isUndef())
        assert(!MO.isPublic());
    

  if (!shouldConsiderInstructionForPrefix(*MI))
    return;

  const auto addFlag = [&OutMI] (auto f) {
    const auto flags = OutMI.getFlags();
    assert((flags & f) == 0);
    OutMI.setFlags(flags | f);
  };

  // We'll mark it protected under three conditions.
  // 1: A explicit output is protected.
  // 2: There are no explicit outputs and an implicit output is marked protected.
  // 3: The instruction has a folded memory operand.
  bool Protected = false;

  // 1: An explicit output is protected.
  Protected |= llvm::any_of(MI->operands(), [] (const MachineOperand &MO) {
    return MO.isReg() && MO.isDef() && !MO.isImplicit() && !MO.isPublic();
  });

  // 2: There are no explicit outputs and an implicit output is marked protected.
  const bool UnprotExpDef = llvm::any_of(MI->operands(), [] (const MachineOperand &MO) {
    return MO.isReg() && MO.isDef() && !MO.isImplicit() && MO.isPublic();
  });
  Protected |= !UnprotExpDef && llvm::any_of(MI->operands(), [] (const MachineOperand &MO) {
    return MO.isReg() && MO.isDef() && MO.isImplicit() && !MO.isPublic();
  });

  // 3: Or if the instruction has a folded memory operand.
  if (hasFoldedLoad(*MI) || hasFoldedStore(*MI)) {
    // This instruction was folded, so we just mark it protected to be safe.
    Protected = true;
    LLVM_DEBUG(dbgs() << "Marking folded instruction as protected: " << *MI);
  }
  
  if (!Protected)
    return;

  LLVM_DEBUG(dbgs() << "Adding PROT prefix to " << *MI);
  addFlag(X86::IP_TPE_PRIVM);

  if (std::getenv("PTEX_VERBOSE"))
    errs() << "Adding PROT prefix: " << *MI;

  // DEBUG
  if (MI->getOpcode() == X86::LEA64r || MI->getOpcode() == X86::LEA64_32r) {
    assert(llvm::any_of(MI->operands(), [] (const auto &MO) {
      return MO.isReg() && MO.isUse() && !MO.isPublic();
    }));
  }
}

}
