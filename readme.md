

# Supplementary material for: 
# Analyzing and Debugging Normative Requirements via Satisfiability Checking

## This repo contains:
- The supplementary material document: [supplementary.pdf](supplementary.pdf)
- LEGOS-SLEEC implementing our approach N-check. Please refer to the [instructions](#instruction-for-launching-n-tool)  for information on how to install it.
- The [nine case studies](#case-studies) used to evaluate LEGOS-SLEEC.

# Instruction for launching LEGOS-SLEEC:
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
    

### Launch LEGOS-SLEEC
`python3 sleecFrontEnd.py`

At this point, an UI window should have popped up.
Edit the text in the window to customize your SLEEC rules

### Case Studies
Please find here, both the initial and corrected normative requirements collected for nine case studies.

1. [ALMI](Case-studies/ALMI.pdf) [(initial,](ALMI/ALMI.sleec)[ corrected)](ALMI/ALMI-Corrected.sleec)
2. [ASPEN](Case-studies/ASPEN.pdf) [(initial,](ASPEN/aspen.sleec)[ corrected)](ASPEN/aspen-corrected.sleec)
3. [AutoCar](Case-studies/AutoCar.pdf) [(initial,](Autocar/Autocar.sleec)[ corrected)](Autocar/Autocar-corrected.sleec)
4. [BSN](Case-studies/BSN.pdf) [(initial,](BSN/BSN.sleec)[ corrected)](BSN/BSN-corrected.sleec)
5. [CSICobot](Case-studies/CSICobot.pdf) [(initial,](CSI/CSI.sleec)[ corrected)](CSI/CSI-corrected.sleec)
6. [DAISY](Case-studies/DAISY.pdf) [(initial,](DAISY/Daisy.sleec)[ corrected)](DAISY/Daisy-corrected.sleec)
7. [DPA](Case-studies/DPA.pdf) [(initial,](gdpr/DPA.sleec)[ corrected)](gdpr/DPA-corrected.sleec)
8. [DressAssist](Case-studies/DressAssist.pdf) [(initial,](dressingAssist/DRESSASSIST.sleec)[ corrected)](dressingAssist/DRESSASSIST-corrected.sleec)
9. [SafeSCAD](Case-studies/SafeSCAD.pdf) [(initial,](safescade/safescade.sleec)[ corrected)](safescade/safescade-corrected.sleec)


