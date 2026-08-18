/-
Copyright (c) 2026 Daniel Lyng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng
-/
module

public import Econlib.Math.Topology.Brouwer
public import Econlib.Math.Topology.ContinuousSelection
public import Econlib.Math.Topology.ConvexHomeomorph
public import Econlib.Math.Topology.FanGlicksberg
public import Econlib.Math.Topology.Kakutani
public import Econlib.Math.Topology.MinkowskiSum
public import Econlib.Math.Topology.Schauder
public import Econlib.Math.Topology.Semicontinuous
public import Econlib.Math.Topology.StrictMonoOn
public import Econlib.Math.Topology.Tychonoff

/-!
# Topology support library

This module collects topological tools for Econlib's equilibrium and optimization developments. It
exposes fixed-point theorems, continuous-selection results, semicontinuity of partial suprema, and
homeomorphisms between compact convex sets and standard domains.

## Main topics

* Fixed points: Brouwer, Schauder, Kakutani, Tychonoff, and Kakutani-Fan-Glicksberg forms.
* Correspondences and selections: Continuous selection from single-valued upper-hemicontinuous
  correspondences and semicontinuity results for compact fibers.
* Convex compact geometry: Homeomorphisms between convex compact sets, unit balls, and unit cubes.

## Tags

topology, fixed point, kakutani, schauder, continuous selection
-/
