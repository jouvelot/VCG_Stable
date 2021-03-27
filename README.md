# VCG Stable
A CoQ/SSReflect formalization project of the General Vickrey-Clarke-Groves (VCG) auction mechanism and VCG for Search auction algorithm and their properties (No positive tranfer, Rationality and (partial) Truthfulness).

Start with the VCG_Search_as_General_VCG.v file to run the proof. Otherwise, add the commented out Requires at the start of the 
General_VCG/mechanism.v file, if you only want to run this one.

See file headers for proper description.

This formalization has been tested using the following running environment on MacOS :

nix-shell -p coqPackages_8_12.coq -p coqPackages_8_12.mathcomp --run \ /Applications/Emacs.app/Contents/MacOS/Emacs

Pierre Jouvelot, MINES ParisTech, PSL University, France

Lucas Massoni Sguerra, MINES ParisTech, PSL University, France

Emilio J. Gallego Arias, Inria Paris, France
