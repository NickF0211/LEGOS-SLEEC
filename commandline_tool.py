import sys
from os.path import dirname, join

sys.path.append(join(dirname(dirname(__file__)), "Analyzer"))
import argparse
from SleecNorm import check_situational_conflict
from sleecParser import read_model_file, check_input_red, check_input_conflict, check_input_concerns, check_input_purpose

SUPPORTED_ANALYSIS_TYPE = ['red', 'c', 'sc', 'con', 'pur']

parser = argparse.ArgumentParser(description='Input to SLEEC Check')
parser.add_argument('filename')
parser.add_argument('type')




if __name__ == "__main__":
    args =  parser.parse_args()
    if args.type not in SUPPORTED_ANALYSIS_TYPE:
        print("Invalid analysis type")
        exit(-1)

    model_str = read_model_file(args.filename)
    if args.type == 'red':
        check_input_red(model_str)
    elif args.type == 'c':
        check_input_conflict(model_str)
    elif args.type == 'con':
        check_input_concerns(model_str)
    elif args.type == 'pur':
        check_input_purpose(model_str)
    elif args.type == 'sc':
        check_situational_conflict(model_str)



