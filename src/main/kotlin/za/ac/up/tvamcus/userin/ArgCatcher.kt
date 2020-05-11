package za.ac.up.tvamcus.userin

import org.apache.commons.cli.*


object ArgCatcher {
    @JvmStatic
    fun main(args: Array<String>) {
        val parser: CommandLineParser = DefaultParser()
        val options: Options = Options()
        val ef: Option = Option(
            "ef", "evaluateFile", true, "Runs an evaluation of your file - reachability of given location by any process is tested by default - args are filename and error location"
        )
        ef.args = 2
        options.addOption(ef)
        options.addOption("l", "liveness", false, "Set evaluation of file to liveness - if this flag is not set it is assumed you are testing for reachability")
        options.addOption("p", "processes", true, "Accepts a comma-separated list of processes ids that should take part in evaluation - if not used all processes take part")
        options.addOption("f", "fair", false, "Enforce fairness")
        options.addOption("h", "help", false, "Prints this help message")
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
}