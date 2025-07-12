#include "PTeXAnalysis.h"

#include "X86.h"

using namespace llvm;
using llvm::X86::PTeXAnalysis_CTS;

bool PTeXAnalysis_CTS::backward_block(MachineBasicBlock &MBB) {
  
}

bool PTeXAnalysis_CTS::backward() {
  bool Changed = false;

  for (MachineBasicBlock &MBB : MF)
    backward_block(MBB); 

  // Forward-propagate intra-block.
  for (MachineBasicBlock &MBB : MF)
    for (MachineInstr &MI : MBB)
      if (allInputsPublic(MI, In[&MI]))
        Changed |= markOutputsPublic(MI, Out[&MI]);

  // Forward-propagate 
}


