# FLOLAC 2024

This repository is meant to store (hopefully) every formal proofs and 
haskell practice code introduced in [FLOLAC 2024](https://flolac.iis.sinica.edu.tw/zh/2024/).

## How to run

If you want to interactively debug the proof, use:
```bash
$ stack ghci
```

Otherwise, if you'll have to adjust main function in [Main.hs](/app/Main.hs), and use:
```bash
$ stack run
```

## Disclaimer

All the haskell code is compilable, but Agda file only contains proof related content, which
is not meant to be compiled and executed by agda compiler.
