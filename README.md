Mechanization (in the Coq proof assistant) of a synthetic many-one reduction from "uniform boundedness of deterministic simple stack machines" to "semi-unification".

Uniform boundedness of deterministic simple stack machines is mechanized as `DSSM_UB` in `SM/DSSM_UB.v`.

Semi-unification is mechanized as `SemiU` in `SemiU/SemiU.v`.

The reduction from `DSSM_UB` to `SemiU` is mechanized as `Theorem DSSM_UB_to_SemiU : DSSM_UB ⪯ SemiU` in `SemiU/DSSM_UB_to_SemiU.v`.

Build instructions: 
```
install Coq (8.10.2) 
cd 2020-fscd-semi-unification
make
```
