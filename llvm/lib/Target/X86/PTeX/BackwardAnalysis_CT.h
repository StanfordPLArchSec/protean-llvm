#pragma once

#include "PTeX/PTeXInfo.h"

namespace llvm::X86 {

// TODO: Rename to BackwardAnalysis_CT.
class BackwardAnalysis_CT : public PTeXInfo {
private:
  PTeXInfo &Parent;

public:
  BackwardAnalysis_CT(PTeXInfo &Parent):
      PTeXInfo(Parent.MF), Parent(Parent) {}

  bool run();

private:
  std::unordered_set<MachineOperand *> PubOps;

  void init();
  bool block(MachineBasicBlock &MBB);
  bool instruction(MachineInstr &MI, PublicPhysRegs &PubRegs);

  bool dataDefsPublic(const MachineInstr &MI, const PublicPhysRegs &PubRegs) const;
  bool backpropSafeForInst(const MachineInstr &MI, const PublicPhysRegs &PubRegs) const;
  bool backpropSafeForInst_sSNI(const MachineInstr &MI, const PublicPhysRegs &PubRegs) const;

  bool erasePubOp(const MachineOperand *MO);
};

}
