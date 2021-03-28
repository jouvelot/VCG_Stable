# VCG (partial)

A Coq/SSReflect formalization project of the General Vickrey-Clarke-Groves (VCG) auction mechanism and VCG for Search auction algorithm, seen as an instance of the general mechnism. In addition, we provide proof of their important properties, namely No positive tranfer, Rationality and (partial, for now, since limited to _stable bid_ changes) Truthfulness.

See the technical report [Towards a Generic CoQ Proof of the Truthfulness of Vickrey–Clarke–Groves Auctions for Search - Short Paper -](report.pdf) in this repository (it's is a bit outdated, and code has been somewhat updated) and also the file headers, for proper description.

## Usage

Start with the VCG_Search_as_General_VCG.v` file to run the whole project. Otherwise, add the commented out `Require` at the start of the 
`General_VCG_mechanism.v` file, if you only want to run this one.

This formalization has been tested using the following running environment on MacOS :

```
nix-shell -p coqPackages_8_12.coq -p coqPackages_8_12.mathcomp --run /Applications/Emacs.app/Contents/MacOS/Emacs
```

## Authors

- Pierre Jouvelot, MINES ParisTech, PSL University, France
- Lucas Massoni Sguerra, MINES ParisTech, PSL University, France
- Emilio J. Gallego Arias, Inria Paris, France
