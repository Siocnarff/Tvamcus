package za.ac.up.tvamcus.feedback

import org.logicng.datastructures.Tristate
import za.ac.up.tvamcus.state.evaluation.State

data class EvaluatorFeedback(
    val satisfiable: Tristate,
    val witness: MutableList<State>,
    val k: Int
)