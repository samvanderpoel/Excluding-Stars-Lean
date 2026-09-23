import DenseGraph.Analysis
import DenseGraph.Asymptotics
import DenseGraph.FiniteModels
import DenseGraph.Graphon
import DenseGraph.Regularity

/-!
# Axiom-free reusable dense-graph library

`DenseGraph` is the stable, neutral import point for the reusable scalar,
graphon, regularity, finite-probability, and asymptotic foundations extracted
from the induced-star development.  It deliberately excludes the project's
published-input instances and every induced-star extremal or structural
module.  `scripts/check_densegraph_import_boundary.py` enforces that closure.
-/
