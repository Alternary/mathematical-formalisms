import copy

theorems = [
    [["s","′"]],
    [["s","𝕴"]],
    [["s","＝"]],
    [["s","∈"]],
    [["s","¬"]],
    [["s","→"]],
    [["s","∀"]],
    [["s","▒"]],
    [["s","A"],["s","B"],["s","AB"]],
    
    [["c","′"]],
    [["c","A"],["c","A′"]],
    [["c","A"],["i","𝕴A"]],
    
    [["i","A"],["w","B"],["w","＝AB"]],
    [["i","A"],["w","B"],["w","∈AB"]],
    [["w","A"],["w","¬A"]],
    [["w","A"],["w","B"],["w","→AB"]],
    [["i","A"],["w","B"],["w","∀AB"]],
    
    [["i","A"],["c","B"],["p","A▒AB"]],
    [["i","A"],["c","B"],["p","AB▒A"]],
    [["i","A"],["p","A▒＝"]],
    [["i","A"],["p","A▒∈"]],
    [["i","A"],["p","A▒¬"]],
    [["i","A"],["p","A▒→"]],
    [["i","A"],["p","A▒∀"]],
    [["i","A"],["s","B"],["s","C"],["p","A▒B"],["p","A▒C"],["p","A▒BC"]],
    [["p","A"],["g","A"]],
    [["g","A"],["g","B"],["g","A▒B"]],
    
    [["w","A"],["w","B"],["w","C"],["w","D"],["w","E"],["t","→→→→→AB→¬C¬DCE→→EA→DA"]],
    [["w","A"],["w","B"],["t","A"],["t","→AB"],["t","B"]],
    
    [["i","A"],["w","B"],["w","C"],["t","→∀A→BC→∀AB∀AC"]],
    [["i","A"],["w","B"],["p","A▒B"],["t","→B∀AB"]],
    [["i","A"],["w","B"],["t","∀AB"]],
    
    [["i","A"],["i","B"],["t","¬∀A¬＝AB"]],
    [["i","A"],["i","B"],["i","C"],["t","→＝AB→＝AC＝BC"]],
    
    [["i","A"],["i","B"],["i","C"],["t","→＝AB→∈AC∈BC"]],
    [["i","A"],["i","B"],["i","C"],["t","→＝AB→∈CA∈CB"]],
    [["i","A"],["i","B"],["i","C"],["g","A▒B▒A▒C"],["t","→∀A¬→→∈AB∈AC¬→∈AC∈AB＝BC"]],
    [["i","A"],["i","B"],["i","C"],["g","A▒B▒A▒C▒B▒C"],["t","¬∀A¬→¬∀B¬∀C→D＝CB∀C¬→→∈CA¬∀A¬¬→∈AB¬∀BD¬→¬∀A¬¬→∈AB¬∀BD∈CA"]],
    [["i","A"],["i","B"],["i","C"],["g","A▒B▒A▒C▒B▒C"],["t","¬∀A¬∀B→∀A→∈AB∈AC∈BA"]],
    [["i","A"],["i","B"],["i","C"],["g","A▒B▒A▒C▒C▒B"],["t","→∈AB¬∀A¬¬→∈AB¬∀C→∈CA¬∈CB"]],
    [["i","A"],["i","B"],["i","C"],["g","A▒B▒A▒C▒B▒C"],["t","¬∀A¬¬→∈BA¬∀B→∈BA¬∀C¬¬→∈BC¬∈CA"]],
    
    [["i","A"],["i","B"],["i","C"],["i","D"],["g","A▒B▒A▒C▒A▒D▒B▒C▒B▒D▒C▒D"],["t","¬∀A¬∀B∀C→¬→∈BC¬∈CD¬∀D¬∀B¬→→¬∀D¬¬→¬→∈BC¬∈CD¬¬→∈BD¬∈DA＝BD¬→＝BD¬∀D¬¬→¬→∈BC¬∈CD¬¬→∈BD¬∈DA"]]
]

variables = ["A","B","C","D","E"]

def substitute(a,b,c):
    return c.replace(a,b)

def restart():
    main()

#then we need a loop for asking the user to input some theorems
def main():
    print("If you wish to list strings, type s")
    print("If you wish to list counters, type c")
    print("If you wish to list individuals, type i")
    print("If you wish to list wffs, type w")
    print("If you wish to list provisos, type p")
    print("If you wish to list proviso groups, type g")
    print("If you wish to list theorems, type t")
    print("If you wish to list all theorems, type a")
    x = input("If you wish to construct a theorem, type the index of an inference rule you wish to instantiate.")
    
    if x in ["s","c","i","w","p","g","t"]:
        for i in range(len(theorems)):
            theorem = theorems[i]
            conclusion = theorem[len(theorem)-1]
            if conclusion[0] == x:
                print(i,":",theorem)
        restart()
    
    if x == "a":
        for i in range(len(theorems)):
            theorem = theorems[i]
            print(i,":",theorem)
        restart()
    
    try:
        #index of inference rule
        infex = int(x)
    except (ValueError):
        print("Incorrect input received!")
        restart()
    
    try:
        hypotheses = copy.deepcopy(theorems[infex])
    except (IndexError):
        print("Index out of range!")
        restart()
    
    conjecture = hypotheses.pop()
    
    for index in range(len(hypotheses)):
        hypothesis = hypotheses[index]
        print("Type the index of the theorem you wish to unify with the hypothesis",hypothesis,".")
        unifier = input("")
        try:
            unifier = int(unifier)
        except (ValueError):
            print("Only integers are accepted!")
            restart()
    
        try:
            #we won't have an inference as a hypothesis, so it's gonna be a simple list singleton
            unifier = theorems[unifier][0]
        except (IndexError):
            print("Index out of range!")
            restart()
    
        if hypothesis[0] != unifier[0]:
            print("The type of the theorem doesn't match the type of the hypothesis!")
            restart()
    
        #is the hypothesis a variable definition?
        if hypothesis[1] in variables:
            #okay so we have a variable definition
            var = hypothesis[1]
            substituent = unifier[1]
            #we gotta do a substitution for all the following hypotheses in hypotheses
            for i in range(index,len(hypotheses)):
                h = hypotheses[i]
                hypotheses[i][1] = substitute(var,substituent,h[1])
            #also do the same substitution for the conjecture
            conjecture[1] = substitute(var,substituent,conjecture[1])
        else:
            if hypothesis[1] != unifier[1]:
                print("The unification has failed")
                restart()
    
    print("The unification has succeeded and the theorem",conjecture,"has been proven.")
    newIndex = len(theorems)
    theorems.append([conjecture])
    print("Its index is",newIndex,".")
    print()
    main()

main()