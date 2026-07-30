import «statements-and-proofs».Exponent7.NumericalEndpoint

/-!
# Trust audit for the conditional exponent-seven package

`CleanMatchingDichotomyStatement reserve` is an explicit proposition argument,
not an axiom.  The declarations below must therefore print only Lean's
standard logical axioms.
-/

#print axioms SimpleGraph.Exponent7.cleanBridgeBatch_of_nodeWellLinked
#print axioms SimpleGraph.Exponent7.shortWideGrid_of_cleanMatchingDichotomy
#print axioms SimpleGraph.Exponent7.gridMinor_of_weakPathOfSetsSystem_of_cleanMatchingDichotomy

#print axioms SimpleGraph.Exponent7.exists_amortizedSlicingDichotomy
#print axioms SimpleGraph.Exponent7.exists_uniformAmortizedSlicingDichotomy
#print axioms SimpleGraph.Exponent7.gridMinor_of_pseudoGrid_noCrossbar

#print axioms SimpleGraph.Exponent7.localCrossbar_or_grid
#print axioms SimpleGraph.Exponent7.gridMinor_of_hairyPathOfSets
#print axioms SimpleGraph.Exponent7.containsGridMinor_of_treewidth_parameters

#print axioms SimpleGraph.Exponent7.exponentSevenLocalThreshold_le
#print axioms SimpleGraph.Exponent7.rounded_exponentSevenLocalThreshold_le
#print axioms SimpleGraph.Exponent7.PolynomialThresholdTemplate7.toParameterChoice
#print axioms SimpleGraph.Exponent7.PolynomialThresholdTemplate7.canonical
#print axioms SimpleGraph.Exponent7.polynomial_grid_minor_theorem7
