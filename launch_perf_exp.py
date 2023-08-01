import subprocess
import glob

SUPPORTED_ANALYSIS_TYPE = ['red', 'c', 'sc', 'con', 'pur']

# replace time with memtime if it is available
measure_tool = "time"
cmd_file = "commandline_tool.py"

# add more case studies here
Case_Study_repo = ['safescade', 'gdpr', 'dressingAssist', 'DAISY', 'CSI', 'BSN', 'Autocar', 'ASPEN', 'ALMI']

# where you want to the result
outfilename = "experiment.txt"

# timeout value for each launch
timeout = 200

# if you want more information
debug = False

with open(outfilename, 'w') as outfile:
    for case_study in Case_Study_repo:
        case_files = glob.glob('{}/*.sleec'.format(case_study))
        for case in case_files:
            for t in SUPPORTED_ANALYSIS_TYPE:
                print('Analyzing {} for {}\n'.format(case, t))
                outfile.write('Analyzing {} for {}\n'.format(case, t))
                try:
                    result = subprocess.run([measure_tool, "python3", cmd_file, case, t], stdout=subprocess.PIPE,
                                            stderr=subprocess.PIPE,
                                            universal_newlines=True,
                                            timeout=timeout)
                    outfile.write(result.stderr)
                    if debug:
                        outfile.write(result.stdout)


                except subprocess.TimeoutExpired as t:
                    outfile.write("timeout {}".format(timeout))

                outfile.flush()