

# Supplementary material for ICSE 2024 submission: 
# Analyzing and Debugging Normative Requirements via Satisfiability Checking

## This repo contains:
- The supplementary material document: [supplementary.pdf](https://anonymous.4open.science/r/N-check-7218/supplementary.pdf)
- N-tool implementing our approach N-check. Please refer to the instructions below for information on how to install it.
- The nine case studies used to evaluate N-tool. Please refer to the the bottom of the page for the case studies.

# Instruction for launching N-Tool:
### prerequisite:
1. Python 3.5 and later


3. z3-solver with python binding:
    `pip install z3-solver` or 
    `pip3 install z3-solver`
    
4. pysmt:
    `pip install pysmt` or 
    `pip3 install pysmt`

5. `pip install ordered-set`

6. `pip install textx`

7. `pip install idle`
    

### Launch AutoCheck
`python3 sleecFrontEnd.py`

At this point, an UI window should have popped up.
Edit the text in the window to customize your SLEEC rules

### Case Examples
[ALMI](https://anonymous.4open.science/r/N-check-7218/ALMI/ALMI.sleec), [ASPEN](https://anonymous.4open.science/r/N-check-7218/ASPEN/aspen.sleec), [Autocar](https://anonymous.4open.science/r/N-check-7218/Autocar/Autocar.sleec), [BSN](https://anonymous.4open.science/r/N-check-7218/BSN/BSN.sleec), [CSI](https://anonymous.4open.science/r/N-check-7218/CSI/CSI.sleec), [DAISY](https://anonymous.4open.science/r/N-check-7218/DAISY/Daisy.sleec), [DressAssist](https://anonymous.4open.science/r/N-check-7218/dressingAssist/DRESSASSIST.sleec), [DPA](https://anonymous.4open.science/r/N-check-7218/gdpr/DPA.sleec), [SafeSCAD](https://anonymous.4open.science/r/N-check-7218/safescade/safescade.sleec)


