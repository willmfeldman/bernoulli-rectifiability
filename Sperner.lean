/-
Copyright (c) 2026 William M. Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/
module

public import Sperner.Basic
public import Sperner.CapSymmetry
public import Sperner.Compactness
public import Sperner.Cone
public import Sperner.EnergyInequality
public import Sperner.Equality
public import Sperner.Equality.Minimizer
public import Sperner.Equality.Rigidity
public import Sperner.Equality.Weak
public import Sperner.FaberKrahn
public import Sperner.GaussIBP
public import Sperner.Harmonic
public import Sperner.Main
public import Sperner.Picone
public import Sperner.Polarization
public import Sperner.Radial
public import Sperner.Reduction
public import Sperner.Semicontinuity
public import Sperner.Vendor.HarmonicBasic
public import Sperner.Vendor.Weyl.DuBoisReymond
public import Sperner.Vendor.Weyl.LaplacianInvariance
public import Sperner.Vendor.Weyl.MeanValue
public import Sperner.Vendor.Weyl.PolarCoord
public import Sperner.Vendor.Weyl.Weyl

/-!
# Sperner's inequality

Root module of the `Sperner` library. It imports every module of the library. The headline
theorem is `Sperner.sperner_half_volume` (`Sperner/Main.lean`), Sperner's inequality (E. Sperner,
Jr., *Zur Symmetrisierung von Funktionen auf Sphären*, Math. Z. 134 (1973), 317–327) in
homogeneous form: a spherical domain carrying a positive Dirichlet eigenfunction with eigenvalue
`n - 1` has at least half the area of the sphere, with equality only for hemispheres.
-/
