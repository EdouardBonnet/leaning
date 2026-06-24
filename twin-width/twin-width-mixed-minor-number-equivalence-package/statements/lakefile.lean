import Lake
open Lake DSL

package TwinWidthMixedMinorNumberEquivalence.Statements where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c5ea00351c28e24afc9f0f84379aa41082b1188f"

lean_lib TwinWidthMixedMinorNumberEquivalence.Statements.Source where
  srcDir := "../source"
  roots := #[
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Contraction.Trigraph,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Contraction.TwinWidth,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Equivalence.FunctionalEquivalence,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Equivalence.Main,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Equivalence.MainContract,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Equivalence.MixedToTwinWidth,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Equivalence.TwinWidthToMixed,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Graph.MixedMinorNumber,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Graph.Partition,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Graph.Theorem14,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Graph.TwinDecomposition,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.Cell,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.Corner,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.DivisionSequence,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.Fusion,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.GridMinor,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.MarcusTardos,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.MixedMinor,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.MixedNumber,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.MixedValue,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.MixedWitness,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.OrderedAdjacency,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.Partition,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.Symmetric,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.Theorem10,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.Theorem10Defs,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Matrix.TwinWidth,
    `TwinWidthMixedMinorNumberEquivalence.Statements.Source.TwinWidth.Order.Divisions
  ]

@[default_target]
lean_lib TwinWidthMixedMinorNumberEquivalence.Statements where
  roots := #[`TwinWidthMixedMinorNumberEquivalence.Statements.Main]
