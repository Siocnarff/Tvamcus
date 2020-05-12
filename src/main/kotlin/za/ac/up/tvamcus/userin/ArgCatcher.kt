package za.ac.up.tvamcus.userin

import org.apache.commons.cli.*


object ArgCatcher {
    @JvmStatic
    fun main(args: Array<String>) {
        val parser: CommandLineParser = DefaultParser()
        val options = setArgOptions()
        val cmd: CommandLine = parser.parse(options, args)
        if(cmd.hasOption("ef")) {
            println("evaluate file")
            println(cmd.getOptionValues("ef")[0])
            println(cmd.getOptionValues("ef")[1])
        } else {
            val formatter = HelpFormatter()
            formatter.printHelp("Tvamcus", options);
        }
    }

    private fun setArgOptions(): Options {
        val options = Options()
        val efr = Option(
            "er",
            "evaluateReachability",
            true,
            "Evaluate reachability by any process in CFG model - args are JSON filename, error location and upper bound."
        )
        efr.args = 3
        options.addOption(efr)
        val efl = Option(
            "el",
            "evaluateLiveness",
            true,
            "Evaluate liveness of all processes in CFG model - args are JSON filename, error location and upper bound."
        )
        efl.args = 3
        options.addOption(efl)
        options.addOption(
            "f",
            "fair",
            false,
            "Enforce fairness."
        )
        options.addOption(
            "h",
            "help",
            false,
            "Print this help message."
        )
        options.addOption(
            "led",
            "locationEncodingDisjunct",
            false,
            "Use disjunction in error location encoding, if flag not specified error location encoding uses conjunction."
        )
        options.addOption(
            "mm",
            "multiModel",
            false,
            "Set evaluation to use the multi-model approach. NoP file must have same name as AllP file, only with _0P appended.")
        options.addOption(
            "p",
            "processes",
            true,
            "Accepts a comma-separated list of processes (by id) that should take part in evaluation, if not specified all processes take part."
        )
        return options;
    }
}