package za.ac.up.tvamcus.formulafactory

import org.logicng.formulas.FormulaFactory
import org.logicng.io.parsers.PropositionalParser
import org.logicng.solvers.MiniSat

object Ff {
    val ff = FormulaFactory()
    val p = PropositionalParser(ff)
    val solver: MiniSat = MiniSat.glucose(ff)
}