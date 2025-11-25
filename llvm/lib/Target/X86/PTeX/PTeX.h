#pragma once

#include <cstdint>
#include <optional>

#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineMemOperand.h"
#include "llvm/Support/CommandLine.h"

namespace llvm::X86 {

extern cl::opt<bool> PrefixProtectedStores;
extern cl::opt<bool> UnprotectAllPointers;
extern cl::opt<bool> SplitCriticalEdges;

enum PTeXMode {
  SBOX,
  CT,
  CTS,
  NCT,
  RAND,
  sSNI = CT,
};

PTeXMode getPTeXMode(const MachineFunction &MF);
PTeXMode getPTeXMode(const MachineInstr &MI);
bool EnablePTeX(const MachineFunction &MF);
bool EnablePTeX(const MachineInstr &MI);

}
