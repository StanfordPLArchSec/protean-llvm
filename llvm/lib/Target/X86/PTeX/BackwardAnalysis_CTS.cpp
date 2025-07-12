#include "BackwardAnalysis_CTS.h"

#include "X86.h"
#include "llvm/CodeGen/MachineInstr.h"
#include "PTeX/PublicPhysRegs.h"
#include "llvm/CodeGen/TargetRegisterInfo.h"
#include "PTeX/PTeXAnalysis.h"

using namespace llvm;
using X86::BackwardAnalysis_CTS;
using X86::PublicPhysRegs;

void BackwardAnalysis_CTS::init() {
  // Initialize from parent.
  for (MachineBasicBlock &MBB : MF) {
    In[&MBB] = Parent.In[&MBB];
    Out[&MBB] = Parent.Out[&MBB];
  }
}

bool BackwardAnalysis_CTS::anyOutputPublic(const MachineInstr &MI, const PublicPhysRegs &PubRegs) const {
  for (const MachineOperand &MO : MI.operands())
    if (MO.isReg() && MO.isDef() && PubRegs.isPublic(MO.getReg()) &&
        !(MO.isImplicit() && regAlwaysPublic(MO.getReg(), *TRI)))
      return true;
  return false;
}

bool BackwardAnalysis_CTS::instruction(MachineInstr &MI, PublicPhysRegs &PubRegs) {
  bool Changed = false;

  // Mark any new public defs.
  for (MachineOperand &MO : MI.operands()) {
    if (MO.isReg() && MO.isDef() && !MO.isUndef() && PubRegs.isPublic(MO.getReg()) && !MO.isPublic()) {
      MO.setIsPublic();
      Changed = true;
    }
  }

  // Are any outputs public?
  const bool any_output_public = anyOutputPublic(MI, PubRegs);

  // Step backward.
  PubRegs.stepBackward(MI);
  if (any_output_public) {
    for (MachineOperand &MO : MI.operands()) {
      if (MO.isReg() && MO.isUse() && !MO.isUndef()) {
        PubRegs.addReg(MO.getReg());
        if (!MO.isPublic()) {
          MO.setIsPublic();
          Changed = true;
        }
      }
    }
  }

  return Changed;
}

bool BackwardAnalysis_CTS::block(MachineBasicBlock &MBB) {
  bool Changed = false;

  // Add the pub-ins of all successors.
  for (MachineBasicBlock *SuccMBB : MBB.successors())
    Changed |= Out[&MBB].addRegs(In[SuccMBB]);

  // Now, transfer across the block, *in reverse order*.
  PublicPhysRegs PubRegs = Out[&MBB];
  for (MachineInstr &MI : llvm::reverse(MBB))
    Changed |= instruction(MI, PubRegs);

  Changed |= In[&MBB].addRegs(PubRegs);

  return Changed;
}

bool BackwardAnalysis_CTS::run() {
  init();

  bool Changed;
  do {
    Changed = false;

    for (MachineBasicBlock *MBB : llvm::post_order(&MF))
      Changed |= block(*MBB);

  } while (Changed);

  return false;
}
