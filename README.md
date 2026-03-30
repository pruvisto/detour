# The Detour Calculus

This development provides an Isabelle/HOL implementation of the *Detour Calculus*, a relational framework to add small indentations to integration contours.

# Contents

The calculus itself is defined in the file `Detour_Calculus.thy`. Additionally, there are the following two auxiliary files:

- `Path_Nhds.thy`: provides filters describing the neighbourhood of a path, i.e. paths with the same beginning and end in the vicinity of a given path
- `Detour_Prerequisites.thy`: various auxiliary facts about complex analysis, winding numbers, paths, topology, homotopy, etc.

The application of the calculus to the valence formula is in the directory `Modular_Forms` and the corresponding Isabelle session. It consists of the following files:

- `Modular_Forms_Library.thy`: various small auxiliary facts
- `Meromorphic_Upper_Half_Plane.thy`: a type `mero_uhp` of functions meromorphic on the upper half of the complex plane
- `Fourier_Expansion_Mero_UHP.thy`: provides the notion of the Fourier expansion of a periodic meromorphic function, and the notions of meromorphicity/holomorphicity at i∞
- `Modular_Forms.thy`: definition of modular forms
- `Argument_Principle_Sparse`: a tweaked version of the Argument Principle from the `HOL-Complex_Analysis` library, provided by Wenda Li
- `Meromorphic_Forms_Valence_Formula.thy`: the proof of the valence formula; this is the only file that contains the actual use of the Detour Calculus

# Building

Building the development requires the development version of Isabelle and the AFP, specifically `isabelle-dev/fc6456571265` and `afp-devel/35caedb97cc1`.

```
    isabelle build -o document=pdf -P : -D .
```
