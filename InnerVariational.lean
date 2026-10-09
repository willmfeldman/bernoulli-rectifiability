/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import InnerVariational.Analysis.HarmonicLimit
public import InnerVariational.Analysis.Harnack
public import InnerVariational.Analysis.SubMeanValue
public import InnerVariational.Applications.AlphaBound
public import InnerVariational.Applications.Classical
public import InnerVariational.Applications.Compactness
public import InnerVariational.Applications.CompactnessQ
public import InnerVariational.Applications.DensityEstimate
public import InnerVariational.Applications.FreeBoundaryLimit
public import InnerVariational.Basic.LipschitzFTC
public import InnerVariational.Basic.Polar
public import InnerVariational.Basic.Setup
public import InnerVariational.Basic.SphereIntegral
public import InnerVariational.Blowup.Approx1D
public import InnerVariational.Blowup.Approx1DQ
public import InnerVariational.Blowup.ChiLimit
public import InnerVariational.Blowup.ChiLimitQ
public import InnerVariational.Blowup.Constancy
public import InnerVariational.Blowup.DomainVariation
public import InnerVariational.Blowup.ExplicitForm
public import InnerVariational.Blowup.Limit
public import InnerVariational.Blowup.OneDim
public import InnerVariational.Blowup.Profile
public import InnerVariational.Blowup.Profile.L2Limits
public import InnerVariational.Blowup.Profile.Limit
public import InnerVariational.Blowup.Profile.Normalization
public import InnerVariational.Blowup.Renormalization
public import InnerVariational.Blowup.RenormalizationQ
public import InnerVariational.Blowup.Renormalized
public import InnerVariational.Blowup.Sobolev
public import InnerVariational.Blowup.Tangential
public import InnerVariational.Blowup.WeakCompactness
public import InnerVariational.Defs.Calculus
public import InnerVariational.Defs.GMT
public import InnerVariational.Defs.HighestDensity
public import InnerVariational.Defs.LaplacianMeasure
public import InnerVariational.Defs.Quantities
public import InnerVariational.Defs.Solutions
public import InnerVariational.Defs.VariationalSolution
public import InnerVariational.Defs.VariationalSolutionQ
public import InnerVariational.Estimates.Dichotomy
public import InnerVariational.Estimates.Dichotomy.Rescale
public import InnerVariational.Estimates.Dichotomy.Setup
public import InnerVariational.Estimates.DichotomyQ
public import InnerVariational.Estimates.DichotomyQ.Setup
public import InnerVariational.Estimates.GeneralPosition
public import InnerVariational.Estimates.Jones
public import InnerVariational.Estimates.L2Subspace
public import InnerVariational.Estimates.L2SubspaceQ
public import InnerVariational.Foundations.Bridge
public import InnerVariational.Foundations.Glue
public import InnerVariational.Foundations.InnerVariation
public import InnerVariational.Frequency.Abstract
public import InnerVariational.Frequency.Abstract.Basic
public import InnerVariational.Frequency.AbstractError
public import InnerVariational.Frequency.AbstractError.Doubling
public import InnerVariational.Frequency.AbstractError.ModN
public import InnerVariational.Frequency.AbstractError.Pinching
public import InnerVariational.Frequency.Concrete
public import InnerVariational.Frequency.Concrete.Basic
public import InnerVariational.Frequency.Concrete.ChangeOfPoint
public import InnerVariational.Frequency.ConcreteQ
public import InnerVariational.Frequency.ConcreteQ.Basic
public import InnerVariational.Frequency.ConcreteQ.ChangeOfPoint
public import InnerVariational.Frequency.ConcreteQ.Rescale
public import InnerVariational.Frequency.SigmaH
public import InnerVariational.Frequency.SigmaHQ
public import InnerVariational.Harmonic.SpernerGlue
public import InnerVariational.Homogeneity.RayCalculus
public import InnerVariational.Homogeneity.TwoPoint
public import InnerVariational.Kernel.BV
public import InnerVariational.Kernel.Energy
public import InnerVariational.Kernel.GradVariation
public import InnerVariational.Kernel.Harmonic
public import InnerVariational.Kernel.IBP
public import InnerVariational.Kernel.RellichPohozaev
public import InnerVariational.Kernel.Rescale
public import InnerVariational.Kernel.Subharmonic
public import InnerVariational.Kernel.VariationalQ
public import InnerVariational.Main.Covering
public import InnerVariational.Main.Distributional
public import InnerVariational.Main.Laplacian
public import InnerVariational.Main.LaplacianDensity
public import InnerVariational.Main.MainTheorem
public import InnerVariational.Main.ModelLaplacian
public import InnerVariational.Main.RieszMeasure
public import InnerVariational.Monotonicity.Blowup
public import InnerVariational.Monotonicity.Density
public import InnerVariational.Monotonicity.DensityQ
public import InnerVariational.Monotonicity.HighestDensity
public import InnerVariational.Monotonicity.HighestDensityQ
public import InnerVariational.Monotonicity.Homogeneity
public import InnerVariational.Monotonicity.Limits
public import InnerVariational.Monotonicity.LimitsQ
public import InnerVariational.Monotonicity.Radial
public import InnerVariational.Monotonicity.RadialQ
public import InnerVariational.Monotonicity.SigmaHQ
public import InnerVariational.NaberValtorta.Covering
public import InnerVariational.NaberValtorta.CoveringLimit
public import InnerVariational.NaberValtorta.Data
public import InnerVariational.NaberValtorta.Discrete
public import InnerVariational.NaberValtorta.Hausdorff
public import InnerVariational.NaberValtorta.Inputs
public import InnerVariational.NaberValtorta.Instance
public import InnerVariational.NaberValtorta.InstanceQ
public import InnerVariational.NaberValtorta.Main
public import InnerVariational.NaberValtorta.MainFrequency
public import InnerVariational.NaberValtorta.MainFrequencyQ
public import InnerVariational.NaberValtorta.MainQ
public import InnerVariational.NaberValtorta.Packing
public import InnerVariational.NaberValtorta.Rectifiable
public import InnerVariational.NaberValtorta.Reifenberg
public import InnerVariational.NaberValtorta.VolumeEstimate
public import InnerVariational.Registry.BV
public import InnerVariational.Registry.FreeBoundary
public import InnerVariational.Registry.GMT
public import InnerVariational.Registry.Harmonic
public import InnerVariational.Registry.Reifenberg
public import InnerVariational.Registry.Sobolev
public import InnerVariational.Regular.Bump
public import InnerVariational.Regular.ChiInteriorQ
public import InnerVariational.Regular.Density
public import InnerVariational.Regular.DensityQ
public import InnerVariational.Regular.HarmonicCone
public import InnerVariational.Regular.Laplacian
public import InnerVariational.Regular.Laplacian.BlowUp
public import InnerVariational.Regular.Laplacian.GaussGreen
public import InnerVariational.Regular.Laplacian.Measure
public import InnerVariational.Regular.Perimeter
public import InnerVariational.Regular.PerimeterQ
public import InnerVariational.Regular.Viscosity
public import InnerVariational.Regular.Viscosity.Classification
public import InnerVariational.Regular.Viscosity.Main
public import InnerVariational.Regular.Viscosity.MainQ
public import InnerVariational.Regular.ZeroGradient
public import InnerVariational.Singular.Annuli
public import InnerVariational.Singular.Chi
public import InnerVariational.Singular.Density
public import InnerVariational.Singular.DensityQ
public import InnerVariational.Singular.FedererCriterion
public import InnerVariational.Singular.FlatPoint
public import InnerVariational.Singular.FlatPointQ
public import InnerVariational.Singular.HeightLimit
public import InnerVariational.Singular.Tangent
public import InnerVariational.Sobolev.Lipschitz
public import InnerVariational.Sobolev.LocalLipschitz
public import InnerVariational.Sobolev.WeakGradient
public import InnerVariational.Statements.Applications
public import InnerVariational.Statements.LipschitzQ
public import InnerVariational.Statements.Main
public import InnerVariational.Vendor.Analysis.BVCompactness
public import InnerVariational.Vendor.Analysis.BallAverage
public import InnerVariational.Vendor.Analysis.Cutoff
public import InnerVariational.Vendor.Analysis.DuBoisReymond
public import InnerVariational.Vendor.Analysis.FrechetKolmogorovCompact
public import InnerVariational.Vendor.Analysis.LaplacianInvariance
public import InnerVariational.Vendor.Analysis.LocalCompactness
public import InnerVariational.Vendor.Analysis.MeanValue
public import InnerVariational.Vendor.Analysis.PolarCoord
public import InnerVariational.Vendor.Analysis.Weyl
public import InnerVariational.Vendor.HarmonicLimit
public import InnerVariational.Vendor.Harnack
public import InnerVariational.Vendor.SubMeanValue

/-!
# InnerVariational

Formalization of Kriventsov–Weiss, *Rectifiability, finite Hausdorff measure, and compactness for
non-minimizing Bernoulli free boundaries* (arXiv:2306.10131). This file imports every module of the
library. The headline theorems are:

* `InnerVariational.Statements.main_theorem`;
* `InnerVariational.Statements.sigmaH_main` and `InnerVariational.Statements.sigmaH_main_frequency`;
* `InnerVariational.Statements.chi_eq_indicator`;
* `InnerVariational.Statements.laplacian_measure_eq`;
* `InnerVariational.Statements.classical_compactness`.
-/
