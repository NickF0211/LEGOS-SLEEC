import base64
import os
from flask import Flask, request, send_file
from flask_cors import CORS
import json
import subprocess
import shutil


rule_header = "from logic_operator import *\n" \
              "from type_constructor import union\n" \
              "import time\n" \
              "from analyzer import check_property_refining\n" \
              "from {input_domin} import *\n"


domain_header = "from type_constructor import create_type, create_action, create_pair_action\n" \
                "type_dict = dict()\n"

main_func = "\nstart = time.time() \n" \
            "is_minimized = {min_sol} \n" \
            "max_vol = {volum_input} \n" \
            "check_property_refining(rule, set(), complete_rules, ACTION, state_action, True, disable_minimization=False, \n" \
                            "min_solution=is_minimized, vol_bound = max_vol, ignore_state_action = True, boundary_case = {bc}, universal_blocking=False)\n" \
            "print(time.time() - start)\n"

property_header = "from input_rule import * \n"

def str2bool(v):
    if isinstance(v, bool):
        return  v
    if v.lower() in ("yes", "true", "t", "1"):
        return "True"
    else:
        return "False"

app = Flask(__name__)
CORS(app)
TIMEOUT = 3000
@app.route("/compiler",methods=["POST"])
def get_query_from_react():
    data = request.get_json()
    content = data["body"]
    # print(content)
    editor_input = json.loads(content)    #now parse the first editor results:
    src_loc = os.path.dirname(os.path.abspath(__file__))
    for key, value in editor_input.items():
        filename = get_translated_filename(key)
        if filename is None:
            print ("{} : {}".format(key, value))
        else:
            with open(filename, 'w') as file:
                if filename == "input_domain.py":
                    file.write(domain_header)
                elif filename == "input_rule.py":
                    file.write(rule_header.format(input_domin = "input_domain"))
                elif filename == "property.py":
                    file.write(property_header)

                editorinput = base64.b64decode(bytes(value, 'utf-8')).decode('utf-8')
                file.write(editorinput)
                min_sol = False
                bc = False
                if filename == "property.py":
                    if "boundaryCaseReduction" in editor_input:
                        bc = str2bool(editor_input["boundaryCaseReduction"])
                    if "minSolution" in editor_input:
                        min_sol = str2bool(editor_input["minSolution"])
                    func_to_wtire = main_func.format(volum_input=editor_input['volume'],
                                                     bc = bc, min_sol = min_sol  )
                    file.write(func_to_wtire)
    try:
        shutil.move("input_domain.py", os.path.join(src_loc, "input_domain.py"))
        shutil.move("input_rule.py", os.path.join(src_loc, "input_rule.py"))
        shutil.move("property.py", os.path.join(src_loc, "property.py"))

        cmd = ["python", os.path.join(src_loc, "property.py")]
        #output = subprocess.check_output(cmd).decode("utf-8")
        process = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        output, stderr = process.communicate(timeout=TIMEOUT)
        if stderr:
            output = "ERROR: {}".format(stderr.decode("utf-8"))
        else:
            output = output.decode("utf-8")
    except subprocess.TimeoutExpired:
        output = "TIMEOUT: {}".format(str(TIMEOUT))
    return output

def get_translated_filename(key):
    if key == "firstEditorInput":
        return "input_domain.py"
    elif key == "secondEditorInput":
        return "input_rule.py"
    elif key == "thirdEditorInput":
        return "property.py"
    else:
        return None

if __name__ == '__main__':
    app.run()