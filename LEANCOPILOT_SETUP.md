# LeanCopilot Setup Summary

**Status**: ✅ Successfully configured and working

## What Was Done

### 1. Version Alignment
- Downgraded from Lean 4.24.0-rc1 to stable **v4.23.0**
- Pinned mathlib to **v4.23.0** release
- Pinned LeanCopilot to **v4.23.0** release

### 2. Dependencies Installed
- **git-lfs** (required for downloading model files from Hugging Face)
  ```bash
  brew install git-lfs
  git lfs install
  ```

### 3. Pre-built Binaries
- Downloaded arm64-macOS binaries from LeanCopilot v4.23.0 release
- Extracted to `.lake/packages/LeanCopilot/.lake/build/lib/`
- Includes:
  - `libctranslate2.dylib` (CTranslate2 inference engine)
  - `libleanffi.dylib` (FFI bridge)
  - `libLeanCopilot.dylib` (main library)

### 4. Models Downloaded
All 4 required models cloned from Hugging Face to `~/.cache/lean_copilot/models/`:
- `ct2-leandojo-lean4-tacgen-byt5-small` (tactic generation)
- `ct2-leandojo-lean4-retriever-byt5-small` (premise retrieval)
- `premise-embeddings-leandojo-lean4-retriever-byt5-small` (embeddings, ~2GB)
- `ct2-byt5-small` (base model)

## Configuration

### lakefile.toml
```toml
[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.23.0"

[[require]]
name = "LeanCopilot"
git = "https://github.com/lean-dojo/LeanCopilot.git"
rev = "v4.23.0"

[[lean_lib]]
name = "PCP"
moreLinkArgs = ["-L./.lake/packages/LeanCopilot/.lake/build/lib", "-lctranslate2"]
```

### lean-toolchain
```
leanprover/lean4:v4.23.0
```

## Usage

### In VSCode
1. Open any `.lean` file
2. Import LeanCopilot: `import LeanCopilot`
3. Use tactics:
   - `suggest_tactics` - Get AI-generated tactic suggestions
   - `search_proof` - Search for complete proofs
   - `select_premises` - Get relevant lemmas

### Building from Command Line
Set the library path before building:
```bash
export DYLD_LIBRARY_PATH=/Users/jalex/repos/pcp-rpg/.lake/packages/LeanCopilot/.lake/build/lib:$DYLD_LIBRARY_PATH
lake build
```

Or use it inline:
```bash
DYLD_LIBRARY_PATH=.lake/packages/LeanCopilot/.lake/build/lib:$DYLD_LIBRARY_PATH lake build
```

## Test File
Created [PCP/Test/Copilot.lean](PCP/Test/Copilot.lean) - builds successfully.

## Why This Works Now

1. **Stable version alignment**: v4.23.0 across Lean/mathlib/LeanCopilot avoids API breakage
2. **Pre-built binaries**: Avoids needing cmake/C++ compiler for CTranslate2
3. **git-lfs**: Required for downloading large model files (embeddings are 2GB+)
4. **Manual model download**: Bypassed any `lake exe` issues by cloning directly

## Key Insights

- LeanCopilot uses **CTranslate2** (C++ inference engine) for fast transformer model execution
- Models are ~2.5GB total (mostly premise embeddings)
- Pre-built releases exist for arm64-macOS since v4.23.0
- The `lakefile.toml` moreLinkArgs is critical for loading libctranslate2
- DYLD_LIBRARY_PATH may be needed for command-line builds but not for VSCode

## References
- [LeanCopilot GitHub](https://github.com/lean-dojo/LeanCopilot)
- [LeanCopilot Paper](https://arxiv.org/abs/2404.12534)
- [LeanDojo Project](https://leandojo.org/)
