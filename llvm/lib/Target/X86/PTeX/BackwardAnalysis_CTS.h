#pragma once

#include "PTeX/PTeXInfo.h"

namespace llvm::X86 {

class BackwardAnalysis_CTS : public PTeXInfo {
private:
  PTeXInfo &Parent;

public:
  BackwardAnalysis_CTS(PTeXInfo &Parent):
      PTeXInfo(Parent.MF), Parent(Parent) {}

  bool run();

private:
  void init();
  bool block(MachineBasicBlock &MBB);
  bool instruction(MachineInstr &MI, PublicPhysRegs &PubRegs);
  bool anyOutputPublic(const MachineInstr &MI, const PublicPhysRegs &PubRegs) const;
};
  
}
