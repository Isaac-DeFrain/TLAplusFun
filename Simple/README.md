# Simple

This is a formal specification of a simple incrementing variable which increments without bound.

## MC

`MC.tla` and `MC.cfg` define a model for the naive specification `Spec`.

## FairMC

`FairMC.tla` and `FairMC.cfg` define a model for the fair specification `FairSpec` which requires another `Incr` step to occur, as long as it stays enabled, in every behavior.
