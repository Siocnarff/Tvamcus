package za.ac.up.tvamcus.state.evaluation

data class State(
    val timestep: String,
    val locationStatus: MutableList<Pair<Int, Int>>,
    val predicateStatus: MutableList<String>,
    val fairnessStatus: MutableList<String>,
    val reRdStatus: Pair<String, String>
)