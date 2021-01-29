num_questions = int(input("How many questions are in this homework? "))

doc = """
\\documentclass[boxes,color=WildStrawberry]{homework}

\\usepackage{macros}

\\input{config}
\\hwnum{HWNUM}
\\duedate{DUEDATE}

\\begin{document}

"""


for qn in range(1, num_questions + 1):
    print(f"----- Question {qn} -----")
    question = input(f"Type question {qn} (leave blank if nothing before parts): ")
    problem = f"\\begin{{problem}}\n{question}\n"
    solution = "\\begin{solution}\n"
    parts = True if "y" in input("Does this question have parts? ") else False
    if parts:
        problem += "\\begin{parts}\n"
        numParts = int(input("how many parts? "))
        for partCount in range(1, numParts + 1):
            part = input(f"ready for part {partCount}: ")
            problem += f"\\part{{{part}}}\\label{{part:{qn}-{partCount}}}\n"
            solution += f"\\ref{{part:{qn}-{partCount}}}\n"
        problem += "\\end{parts}\n"

    problem += "\\end{problem}"
    solution += "\\end{solution}"

    doc += f"{problem}\n\n{solution}\n\n"

doc += "\\end{document}"

print(doc)