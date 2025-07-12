#pragma once

#include <cstdint>
#include <optional>

#include "llvm/CodeGen/MachineInstr.h"
#include "llvm/CodeGen/MachineMemOperand.h"
#include "llvm/Support/CommandLine.h"

namespace llvm::X86 {

bool EnablePTeX();
extern cl::opt<bool> PrefixProtectedStores;
extern cl::opt<bool> UnprotectAllPointers;
extern cl::opt<bool> SplitCriticalEdges;

enum PTeXMode {
  SBOX,
  CT,
  CTS,
  NCT,
  sSNI = CT,
};

PTeXMode getPTeXMode();

}
