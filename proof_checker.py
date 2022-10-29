#a proof checker for a predicate calculus with substitution, equality, zfc set theory, and distinct variable provisos. basically the set theory metamath system which is based on a system of tarski.

UNARYCONNECTIVES = ["¬"]

BINARYCONNECTIVES = ["∨","∧","→","↔"]

QUANTIFIERS = ["∀","∃"]

BINARYPREDICATECONSTANTS = ["=","∈"]

def UNARYCONNECTIVE(unaryconnective) -> bool:
    return unaryconnective in UNARYCONNECTIVES

def BINARYCONNECTIVE(binaryconnective) -> bool:
    return binaryconnective in BINARYCONNECTIVES

def QUANTIFIER(quantifier) -> bool:
    return quantifier in QUANTIFIERS

def COUNTER(counter) -> bool:
    if counter == "":
        return True
    for i in counter:
        if not i == "′":
            return False
    return True

def DECIMALNUMBER(decimalnumber) -> bool:
    try:
        int(decimalnumber)
    except:
        return False
    return True

ATOMICPROPOSITIONSYMBOLS = [i for i in "𝒂𝒃𝒄𝒅𝒆𝒇𝒈𝒉𝒊𝒋𝒌𝒍𝒎"]

def ATOMICPROPOSITIONSYMBOL(atomicpropositionsymbol) -> bool:
    return atomicpropositionsymbol in ATOMICPROPOSITIONSYMBOLS

def ATOMICPROPOSITION(atomicproposition) -> bool:
    return ATOMICPROPOSITIONSYMBOL(atomicproposition[0]) and ( COUNTER(atomicproposition[1]) or DECIMALNUMBER(atomicproposition[1]) )

INDIVIDUALSYMBOLS = [i for i in "𝒏𝒐𝒑𝒒𝒓𝒔𝒕𝒖𝒗𝒘𝒙𝒚𝒛"]

def INDIVIDUALSYMBOL(individualsymbol) -> bool:
    return individualsymbol in INDIVIDUALSYMBOLS

def INDIVIDUAL(individual: tuple) -> bool:
    return INDIVIDUALSYMBOL(individual[0]) and ( COUNTER(individual[1]) or DECIMALNUMBER(individual[1]) )

FUNCTIONSYMBOLS = [i for i in "𝑨𝑩𝑪𝑫𝑬𝑭𝑮𝑯𝑰𝑱𝑲𝑳𝑴"]

def FUNCTIONSYMBOL(functionsymbol) -> bool:
    return functionsymbol in FUNCTIONSYMBOLS

def TERM(term) -> bool:
    if INDIVIDUAL(term):
        return True
    elif len(term[0]) == 3:
        if not FUNCTIONSYMBOL(term[0][0]):
            return False
        elif not COUNTER(term[0][1]) and not DECIMALNUMBER(term[0][1]):
            return False
        elif term[0][2] == "":
            return TERM(term[1])
        elif DECIMALNUMBER(term[0][2]):
            return term[0][2] == len(term[1])
        return False
    return False

PREDICATESYMBOLS = [i for i in "𝑵𝑶𝑷𝑸𝑹𝑺𝑻𝑼𝑽𝑾𝑿𝒀𝒁"]

def PREDICATESYMBOL(predicatesymbol) -> bool:
    return predicatesymbol in PREDICATESYMBOLS

def WFF(wff) -> bool:
    if ATOMICPROPOSITION(wff):
        return True
    elif UNARYCONNECTIVE(wff[0]):
        return WFF(wff[1])
    elif BINARYCONNECTIVE(wff[1]):
        return WFF(wff[0]) and WFF(wff[2])
    elif QUANTIFIER(wff[0]):
        return INDIVIDUAL(wff[1]) and WFF(wff[2])
    elif wff[1] in BINARYPREDICATECONSTANTS:
        return TERM(wff[0]) and TERM(wff[2])
    elif len(wff[0]) == 3:
        if not PREDICATESYMBOL(wff[0][0]):
            return False
        elif not COUNTER(wff[0][1]) and not DECIMALNUMBER(wff[0][1]):
            return False
        elif wff[0][2] == "":
            return TERM(wff[1])
        elif DECIMALNUMBER(wff[0][2]):
            return wff[0][2] == len(wff[1])
        return False
    return False

def PROVISO(proviso: list) -> bool:
    for i in proviso:
        for j in i:
            if not ATOMICPROPOSITION(j) or INDIVIDUAL(j):
                return False
    return True

def REWRITE(wff):
    if wff[0] == "¬":
        return ("¬",REWRITE(wff[1]))
    elif wff[0] == "∀":
        return ("∀",wff[1],REWRITE(wff[2]))
    elif wff[0] == "∃":
        return ("¬",("∀",wff[1],("¬",REWRITE(wff[2]))))
    elif not len(wff) == 3:
        return wff
    elif wff[1] == "→":
        return (REWRITE(wff[0]),"→",REWRITE(wff[2]))
    elif wff[1] == "∨":
        return (("¬",REWRITE(wff[0])),"→",REWRITE(wff[2]))
    elif wff[1] == "∧":
        return ("¬",(REWRITE(wff[0]),"→",("¬",REWRITE(wff[2]))))
    elif wff[1] == "↔":
        a = REWRITE(wff[0])
        b = REWRITE(wff[2])
        return ("¬",((a,"→",b),"→",("¬",(b,"→",a))))
    else:
        return wff

def SHAREDELEMENTS(one,two) -> bool:
    #return if they have the same elements wherever
    for element in one:
        if not element in two:
            return False
    for element in two:
        if not element in one:
            return False
    return True

def SUBSTITUTIONLIST(one,two) -> list:
    #let's do this in the right order this time around, so two is an instance of one
    #it takes two phrases and returns what substitutions are required to make one two.
    
    ISFUNCTION = False
    try:
        ISFUNCTION = FUNCTIONSYMBOL(one[0][0])
    except:
        pass
    ISPREDICATE = False
    try:
        ISPREDICATE = PREDICATESYMBOL(one[0][0])
    except:
        pass
    
    if ATOMICPROPOSITION(one) or INDIVIDUAL(one):
        return [(one,two)]
    elif ISFUNCTION or ISPREDICATE:
        #I do still have to return something so that when I deal the substitutions, the functions and predicates will be put there as well. However, this means that fulfilled functions may be replaced by any term and fulfilled predicates by any wff... I mean, it peobably doesn't break soundness, but it feels wrong, I could restrict it so that I also check whether the replacement is itself a function or a predicate as well.
        return [(one,two)]
    elif UNARYCONNECTIVE(one[0]):
        return SUBSTITUTIONLIST(one[1],two[1])
    elif QUANTIFIER(one[0]):
        return SUBSTITUTIONLIST(one[1],two[1])+SUBSTITUTIONLIST(one[2],two[2])
    elif len(one) == 3:
        #uniconditional or binary predicate constant
        return SUBSTITUTIONLIST(one[0],two[0])+SUBSTITUTIONLIST(one[2],two[2])

def SUBSTITUTE(one,substitution: tuple):
    #takes one substitution and applies it to a formula or a proviso
    
    ISFUNCTION = False
    try:
        ISFUNCTION = FUNCTIONSYMBOL(one[0][0])
    except:
        pass
    ISPREDICATE = False
    try:
        ISPREDICATE = PREDICATESYMBOL(one[0][0])
    except:
        pass
    if type(one) == list:
        #provisos
        return [SUBSTITUTE(proviso,substitution) for proviso in one]
    elif one == substitution[0]:
        return substitution[1]
    elif ATOMICPROPOSITION(one) or INDIVIDUAL(one) or ISFUNCTION or ISPREDICATE:
        return one
    elif UNARYCONNECTIVE(one[0]):
        return (one[0],SUBSTITUTE(one[1],substitution))
    elif QUANTIFIER(one[0]):
        return (one[0],SUBSTITUTE(one[1],substitution),SUBSTITUTE(one[2],substitution))
    elif len(one) == 3:
        return (SUBSTITUTE(one[0],substitution),one[1],SUBSTITUTE(one[2],substitution))
    elif one[1] == "This is just a temporary substitution":
        return one
    elif len(one) == 2:
        #proviso
        return (SUBSTITUTE(one[0],substitution),SUBSTITUTE(one[1],substitution))

def MORESUBSTITUTE(one,substitutions: list):
    #substitute with lists
    a = one
    for substitution in substitutions:
        a = SUBSTITUTE(a,substitution)
    return a

def SIMULTANEOUSSUBSTITUTION(one,substitutionlist):
    #performs substitutions to a pair of a formula and a proviso.
    formula = one[0]
    proviso = one[1]
    
    #first, change every atomic proposition and individual and then apply the substitutions for the changed stuff. then you done.
    
    #so I should get the substitutionlist of one and one, then I should replace every second element of every substitution in the list with a tuple containing the second element and "This is just a temporary substitution"
    
    firstformulasubstitutions = [(i[0],(i[0],"This is just a temporary substitution")) for i in SUBSTITUTIONLIST(formula,formula)]
    firstformula = MORESUBSTITUTE(formula,firstformulasubstitutions)
    lastsubstitutions = [((i[0],"This is just a temporary substitution"),i[1]) for i in substitutionlist]
    secondformula = MORESUBSTITUTE(firstformula,lastsubstitutions)
    firstprovisosubstitutions = [(i,(i,"This is just a temporary substitution")) for i in [j[0] for j in proviso]+[j[1] for j in proviso]]
    temporaryproviso = MORESUBSTITUTE(proviso,firstprovisosubstitutions)
    secondproviso = MORESUBSTITUTE(temporaryproviso,lastsubstitutions)
    #parse the complex proviso
    thirdproviso = []
    #just get the list of individuals and atoms in the second element of the proviso. Of course, substitutionlist(proviso,proviso) does do that, it just gets the pairs, you know. but it has duplicates, but it alright
    for i in secondproviso:
        if INDIVIDUAL(i[0]):
            #individuals turn into fulfilled functions or individuals, fulfilled functions can be ignored
            thirdproviso += [(i[0],substitution[0]) for substitution in SUBSTITUTIONLIST(i[1],i[1])]
    #btw, I can recurse the set stuff like:
    #[i for i in [a for a in [b for b in []]]]
    return (secondformula,thirdproviso)

def INSTANCE(one,two) -> bool:
    #two is an instance of one
    #I gotta check the well formedness of one in the way that I gotta check WFF and PROVISO, you know.
    if not WFF(two[0]) and PROVISO(two[1]):
        return False
    onerewrite = (REWRITE(one[0]),one[1])
    tworewrite = (REWRITE(two[0]),two[1])
    #first generate the substitutions from them and then apply them simultaneously and then check whether members are shared with the proviso and the supposed proviso
    simultaneoussubstitution = SIMULTANEOUSSUBSTITUTION(onerewrite,SUBSTITUTIONLIST(onerewrite[0],tworewrite[0]))
    if not simultaneoussubstitution[0] == tworewrite[0]:
        #the formulas aren't compatible
        return False
    if not SHAREDELEMENTS(simultaneoussubstitution[1],tworewrite[1]):
        #the provisos aren't compatible
        return False
    return True

def RELEVANTPROVISOS(one):
    formula = one[0]
    proviso = one[1]
    variables = [i[0] for i in SUBSTITUTIONLIST(formula,formula)]
    relevantprovisos = []
    for i in proviso:
        for j in i:
            if not j in variables:
                relevantprovisos.append(i)
                break
    return relevantprovisos

LOGICALSYMBOLS = {"=":1,"∈":1,"∀":1,"∃":1,"¬":2,"∨":3,"∧":4,"→":5,"↔":6}

def ranking(string):
    parenthesis = 0
    rank = -1
    position = -1
    if len(string) == 1:
        if string in LOGICALSYMBOLS:
            return (0,LOGICALSYMBOLS[string])
        return (0,0)
    for i in range(len(string)-1,-1,-1):
        if string[i] == "(":
            parenthesis += 1
        elif string[i] == ")":
            parenthesis -= 1
        elif parenthesis == 0:
            if ranking(string[i])[1] > rank:
                rank = ranking(string[i])[1]
                position = i
    if string[position] in ["∀","∃"] or rank == 2:
        position = 0
    return (position,rank)

def CONVERT(string):
    position = ranking(string)[0]
    rank = ranking(string)[1]
    if rank < 0:
        return CONVERT(string[1:-1])
    elif rank == 0:
        if ATOMICPROPOSITIONSYMBOL(string[0]) or INDIVIDUALSYMBOL(string[0]):
            return (string[0],string[1:])
        elif FUNCTIONSYMBOL(string[0]) or PREDICATESYMBOL(string[0]):
            one = string[:string.find("(")]
            two = string[string.find("("):][1:-1]
            counter = one.count("′")*"′"
            if "#" in one:
                counter = one[1:one.find("#")] 
            arity = one[max(one.find("′")+one.count("′"),one.find("#")+1,1):]
            try:
                arity = int(arity)
            except:
                arity = 1
            a = ""
            parenthesis = 0
            for i in two:
                if i == "(":
                    parenthesis += 1
                    a += "("
                elif i == ")":
                    parenthesis -= 1
                    a += ")"
                elif parenthesis == 0 and i == ",":
                    a += "."
                else:
                    a += i
            return ((one[0],counter,arity),[CONVERT(i) for i in a.split(".")])
    elif rank == 2 and position == 0:
        return (string[0],CONVERT(string[1:]))
    elif rank == 1 and position == 0:
        one = string.find("(")
        for i in range(1,string.find("(")):
            if string[i] in ["∀","∃"]:
                one = i
                break
        return (string[0],CONVERT(string[1:one]),CONVERT(string[one:]))
    elif rank >= 1:
        return (CONVERT(string[:position]),string[position],CONVERT(string[1+position:]))

def flatten(x):
    if type(x) in [tuple,list]:
        a = ""
        for i in x:
            a += flatten(i)
        return a
    elif type(x) == str:
        return x
    elif type(x) == int:
        return str(x)

def lessranking(formula) -> int:
    #takes a formula and returns its rank and not the position
    #could be used elsewhere as well
    
    ISFUNCTION = False
    try:
        ISFUNCTION = FUNCTIONSYMBOL(formula[0][0])
    except:
        pass
    ISPREDICATE = False
    try:
        ISPREDICATE = PREDICATESYMBOL(formula[0][0])
    except:
        pass
    if ATOMICPROPOSITION(formula) or INDIVIDUAL(formula) or ISFUNCTION or ISPREDICATE:
        return 0
    elif len(formula) == 2:
        return ranking(formula[0])[1]
    elif len(formula) == 3:
        if BINARYCONNECTIVE(formula[1]) or formula[1] in BINARYPREDICATECONSTANTS:
            return ranking(formula[1])[1]
        elif QUANTIFIER(formula[0]):
            return 1
        else:
            #nonlogical, well, I mean, isn't equality and such also nonlogical
            return 0

def laconic(formula):
    ll = ""
    lr = ""
    rl = ""
    rr = ""
    if lessranking(formula) == 0:
        #adding the hashtag
        if len(formula) == 2:
            if len(formula[0]) == 3:
                try:
                    int(formula[0][1])
                    return flatten(((formula[0][0],formula[0][1]+"#",formula[0][2]),formula[1])) 
                except:
                    pass
        #nonlogical, should just make a function that flattens an array or a tuple into a string.
        return flatten(formula)
    elif len(formula) == 2:
        #negation
        if 2 < lessranking(formula[1]):
            return formula[0]+"("+laconic(formula[1])+")"
        else:
            return formula[0]+laconic(formula[1])
    elif QUANTIFIER(formula[0]):
        if 1 < lessranking(formula[2]) and len(formula[2]) == 3:
            return flatten(formula[:2])+"("+laconic(formula[2])+")"
        else:
            return flatten(formula[:2])+laconic(formula[2])
    elif len(formula) == 3:
        if ranking(formula[1])[1] < lessranking(formula[0]):
            ll = "("
            lr = ")"
        if ranking(formula[1])[1] <= lessranking(formula[2]):
            rl = "("
            rr = ")"
        return ll+laconic(formula[0])+lr+formula[1]+rl+laconic(formula[2])+rr

def morelaconic(t: tuple):
    formula = t[0]
    proviso = t[1]
    p = ""
    for i in proviso:
        p += "$"+laconic(i[0])+","+laconic(i[1])
    a = laconic(formula)+p
    b = "＃＄（），＝𝟎𝟏𝟐𝟑𝟒𝟓𝟔𝟕𝟖𝟗"
    c = "#$(),=0123456789"
    for i in range(10):
        a = a.replace(c[i],b[i])
    return a

#the characters of the object language are these:
#   ′＃＄（），＝∈∀∃¬∨∧→↔𝑨𝑩𝑪𝑫𝑬𝑭𝑮𝑯𝑰𝑱𝑲𝑳𝑴𝑵𝑶𝑷𝑸𝑹𝑺𝑻𝑼𝑽𝑾𝑿𝒀𝒁𝒂𝒃𝒄𝒅𝒆𝒇𝒈𝒉𝒊𝒋𝒌𝒍𝒎𝒏𝒐𝒑𝒒𝒓𝒔𝒕𝒖𝒗𝒘𝒙𝒚𝒛𝟎𝟏𝟐𝟑𝟒𝟓𝟔𝟕𝟖𝟗

def LESSCONVERT(string):
    #the function naming conventions kind of became awful. well, whatever
    a = "′#$(),=∈∀∃¬∨∧→↔𝑨𝑩𝑪𝑫𝑬𝑭𝑮𝑯𝑰𝑱𝑲𝑳𝑴𝑵𝑶𝑷𝑸𝑹𝑺𝑻𝑼𝑽𝑾𝑿𝒀𝒁𝒂𝒃𝒄𝒅𝒆𝒇𝒈𝒉𝒊𝒋𝒌𝒍𝒎𝒏𝒐𝒑𝒒𝒓𝒔𝒕𝒖𝒗𝒘𝒙𝒚𝒛0123456789"
    b = "'＃＄（），＝<§½-%&>_ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz𝟎𝟏𝟐𝟑𝟒𝟓𝟔𝟕𝟖𝟗"
    c = string
    for i in range(len(b)):
        c = c.replace(b[i],a[i])
    return c

def MORECONVERT(string):
    #converts "a$x,y"
    a = LESSCONVERT(string).split("$")
    formula = a[0]
    proviso = a[1:]
    for i in range(len(proviso)):
        s = proviso[i].split(",")
        proviso[i] = (CONVERT(s[0]),CONVERT(s[1]))
    return (CONVERT(formula),proviso)

def PROOFCONVERT(proof):
    rows = proof.split("\n")
    neoproof = []
    for row in rows:
        a = row.split(".")
        c = a[:-1]
        if not len(c) == 1:
            for i in range(1,len(c)):
                c[i] = int(c[i])-1
        neoproof.append((c,MORECONVERT(a[-1])))
    return neoproof

#as you can see, these are not postulate schemas, they are actual proper postulates. the reason that is possible is that substitution may be applied to them when instantiating them. this simply shifts the schemas to the substitution rule. we could obviously have used schemes as well, it never hurts to use more schemes. however, stating the postulates like this exemplifies the actual underlying language more and it shortens the axiomatization a bit as well, when we don't have to use metavariables and such.
PROPOSITIONALCALCULUS = [MORECONVERT("𝒂→(𝒃→𝒂)"),MORECONVERT("𝒂→(𝒃→𝒄)→(𝒂→𝒃→(𝒂→𝒄))"),MORECONVERT("¬𝒂→¬𝒃→(𝒃→𝒂)")]

PREDICATECALCULUS = [MORECONVERT("∀𝒙(𝒂→𝒃)→(∀𝒙(𝒂)→∀𝒙(𝒃))"),MORECONVERT("𝒂→∀𝒙(𝒂)$𝒙,𝒂")]

EQUALITY = [MORECONVERT("¬∀𝒙(¬𝒙=𝒚)"),MORECONVERT("𝒙=𝒚→(𝒙=𝒛→𝒚=𝒛)")]

SETTHEORY = [MORECONVERT("∀𝒙(𝒙∈𝒚↔𝒙∈𝒛)→𝒚=𝒛$𝒙,𝒚$𝒙,𝒛$𝒚,𝒛"),MORECONVERT("∀𝒛∃𝒚∀𝒛(∀𝒚(𝒂)→𝒛=𝒚)→∃𝒚∀𝒛(𝒛∈𝒚↔∃𝒛(𝒙∈𝒛∧∀𝒚(𝒂)))$𝒙,𝒚$𝒙,𝒛$𝒙,𝒘$𝒚,𝒛$𝒚,𝒘$𝒛,𝒘"),MORECONVERT("∃𝒙∀𝒚(∀𝒛(𝒛∈𝒚→𝒛∈𝒘)→𝒚∈𝒙)$𝒙,𝒚$𝒙,𝒛$𝒙,𝒘$𝒚,𝒛$𝒚,𝒘$𝒛,𝒘"),MORECONVERT("∃𝒙∀𝒚(∃𝒛(𝒚∈𝒛∧𝒛∈𝒘)→𝒚∈𝒙)$𝒙,𝒚$𝒙,𝒛$𝒙,𝒘$𝒚,𝒛$𝒚,𝒘$𝒛,𝒘"),MORECONVERT("∃𝒙(𝒛∈𝒚)→∃𝒛(𝒙∈𝒚∧∀𝒛(𝒛∈𝒙→¬𝒛∈𝒚))$𝒙,𝒚$𝒙,𝒛$𝒚,𝒛"),MORECONVERT("∃𝒙(𝒚∈𝒙∧∀𝒛(𝒛∈𝒙→∃𝒘(𝒛∈𝒘∧𝒘∈𝒙)))$𝒙,𝒚$𝒙,𝒛$𝒙,𝒘$𝒚,𝒛$𝒚,𝒘$𝒛,𝒘")]

AXIOMOFCHOICE = [MORECONVERT("∃𝒙∀𝒚∃𝒛∀𝒘((𝒙∈𝒗∧(𝒚∈𝒙→𝒛∈𝒗∧¬𝒙=𝒛∧𝒚∈𝒛))∨(¬𝒙∈𝒗∧(𝒚∈𝒗→𝒛∈𝒚∧𝒛∈𝒙∧(𝒘∈𝒚∧𝒘∈𝒙→𝒘=𝒛))))$𝒙,𝒚$𝒙,𝒛$𝒙,𝒘$𝒙,𝒗$𝒚,𝒛$𝒚,𝒘$𝒚,𝒗$𝒛,𝒘$𝒛,𝒗$𝒘,𝒗")]

POSTULATES = PROPOSITIONALCALCULUS + PREDICATECALCULUS + EQUALITY + SETTHEORY + AXIOMOFCHOICE

THEOREMS = {}
for i in range(len(POSTULATES)):
    #making it so that we don't have postulate 0 but we start from 1
    THEOREMS[str(i+1)] = POSTULATES[i]

def PROOF(proof: list) -> bool:
    #a row in a proof is a tuple of an array of strings and a tuple of a formula and a proviso
    for theorem in proof:
        one = theorem[0]
        two = theorem[1]
        formula = two[0]
        proviso = two[1]
        if len(one) == 1:
            if not INSTANCE(THEOREMS[one[0]],two):
                return False
        elif one[0] == "m":
            if not proof[int(one[2])][1][0] == (proof[int(one[1])][1][0],"→",formula) or not SHAREDELEMENTS(RELEVANTPROVISOS((formula,proof[int(one[2])][1][1]+proof[int(one[1])][1][1])),proviso):
                return False
        elif one[0] == "g":
            if not formula[0] == "∀" or not INDIVIDUAL(formula[1]) or not (formula[2],proviso) == proof[int(one[1])][1]:
                return False
        elif one[0] == "s":
            if not INSTANCE(proof[int(one[1])][1],two):
                return False
    #try to find a new name for a theorem
    i = len(POSTULATES)+1
    while i < 999:
        if not str(i) in THEOREMS:
            THEOREMS[str(i)] = proof[-1][1]
            break
        i += 1
    return True

def MOREPROOF(x):
    return PROOF(PROOFCONVERT(x))

print(MOREPROOF("""5.𝒂→∀𝒙𝒂$𝒙,𝒂
s.1.𝒃→∀𝒙𝒃$𝒙,𝒃"""))

print(INSTANCE(MORECONVERT(LESSCONVERT("a>b>a")),MORECONVERT(LESSCONVERT("c>a>c"))))

def STABLEPROOF(proof):
    try:
        return PROOF(proof)
    except:
        return False

print(PROOF(PROOFCONVERT("1.a>(a>a)")))

print(PROOF(PROOFCONVERT("""1.a>(a>a)
1.a>(a>a>a)
2.a>(a>a>a)>(a>(a>a)>(a>a))
m.2.3.(a>(a>a)>(a>a))
m.1.4.a>a
1.a>(a>a>a)
1.a>(a>a>a)""")))

print(PROOF(PROOFCONVERT("""1.a>(a>a)
1.a>(a>a>a)
2.a>(a>a>a)>(a>(a>a)>(a>a))
m.2.3.(a>(a>a)>(a>a))
m.1.4.a>a""")))

print(PROOF(PROOFCONVERT("""18.a>a
g.1.§x(a>a)
s.2.§y(b>b)""")))

print(PROOF(PROOFCONVERT("""5.a>§x(a)$x,a""")))
print(INSTANCE(MORECONVERT("a>§x(a)$x,a"),THEOREMS["5"]))

print(MOREPROOF("""14.∃𝒙∀𝒚∃𝒛∀𝒘((𝒙∈𝒗∧(𝒚∈𝒙→𝒛∈𝒗∧¬𝒙=𝒛∧𝒚∈𝒛))∨(¬𝒙∈𝒗∧(𝒚∈𝒗→𝒛∈𝒚∧𝒛∈𝒙∧(𝒘∈𝒚∧𝒘∈𝒙→𝒘=𝒛))))$𝒙,𝒚$𝒙,𝒛$𝒙,𝒘$𝒙,𝒗$𝒚,𝒛$𝒚,𝒘$𝒚,𝒗$𝒛,𝒘$𝒛,𝒗$𝒘,𝒗
g.1.∀𝒗∃𝒙∀𝒚∃𝒛∀𝒘((𝒙∈𝒗∧(𝒚∈𝒙→𝒛∈𝒗∧¬𝒙=𝒛∧𝒚∈𝒛))∨(¬𝒙∈𝒗∧(𝒚∈𝒗→𝒛∈𝒚∧𝒛∈𝒙∧(𝒘∈𝒚∧𝒘∈𝒙→𝒘=𝒛))))$𝒙,𝒚$𝒙,𝒛$𝒙,𝒘$𝒙,𝒗$𝒚,𝒛$𝒚,𝒘$𝒚,𝒗$𝒛,𝒘$𝒛,𝒗$𝒘,𝒗
g.2.∀𝒗∀𝒗∃𝒙∀𝒚∃𝒛∀𝒘((𝒙∈𝒗∧(𝒚∈𝒙→𝒛∈𝒗∧¬𝒙=𝒛∧𝒚∈𝒛))∨(¬𝒙∈𝒗∧(𝒚∈𝒗→𝒛∈𝒚∧𝒛∈𝒙∧(𝒘∈𝒚∧𝒘∈𝒙→𝒘=𝒛))))$𝒙,𝒚$𝒙,𝒛$𝒙,𝒘$𝒙,𝒗$𝒚,𝒛$𝒚,𝒘$𝒚,𝒗$𝒛,𝒘$𝒛,𝒗$𝒘,𝒗"""))

print(MOREPROOF("18.P'2(x,y)>P'2(x,y)"))

print(MOREPROOF("18.P(F'2(x,y))>P1(F'2(x,y))"))

print(PROOF(PROOFCONVERT("""5.𝒂→∀𝒙𝒂$𝒙,𝒂
s.1.𝒚=𝒛→∀𝒙(𝒚=𝒛)$𝒙,𝒚$𝒙,𝒛""")))

print(CONVERT(LESSCONVERT("P1(x)>Q'2(x,y)>R2#3(x,y,z)>S1(x)")))
print(WFF(CONVERT(LESSCONVERT("P(x)>Q'2(x,y)>R2#3(x,y,z)>S1(x)"))))

def laconize(theorems):
    #laconize THEOREMS
    for theorem in theorems:
        print(theorem,"is laconically",morelaconic(theorems[theorem]))

laconize(THEOREMS)

def polisher(formula):
    if lessranking(formula) == 0:
        #adding the hashtag
        if len(formula) == 2:
            if len(formula[0]) == 3:
                try:
                    int(formula[0][1])
                    return flatten(((formula[0][0],formula[0][1]+"#",formula[0][2]),formula[1])) 
                except:
                    pass
        #nonlogical, should just make a function that flattens an array or a tuple into a string.
        return flatten(formula)
    elif len(formula) == 2:
        return formula[0]+polisher(formula[1])
    elif QUANTIFIER(formula[0]):
        return flatten(formula[:2])+polisher(formula[2])
    elif len(formula) == 3:
        return formula[1]+polisher(formula[0])+polisher(formula[2])

def polisher2(formul):
    formula = formul + ""
    return polisher(CONVERT(LESSCONVERT(formula)))

def CONVERT2(x):
    y = REWRITE(CONVERT(LESSCONVERT(x)))
    y = polisher(y)
    #y = laconic(y)
    return y

#print(polisher2("﻿∃x(∃y(∀z(a→z=y))→∀z(z∈x↔∃x(x∈y∧∀ya)))"))
#print(polisher2("﻿﻿∃x(∃y(∀z(a→z=y))→∀z(z∈x↔∃x(x∈y∧∀ya)))"))
#print(polisher2("﻿﻿½x(½y(§z(a>z=y))>§z(z<x_½x(x<y&§ya)))"))
#print(CONVERT2("½x(½y§z(a>z=y)>§z(z<x_½x(x<y&§ya)))"))
#print(CONVERT2("½x§y(§x(x<y>x<z)>y<x)"))
#print(CONVERT2("(x<y>½x(x<y&§z(z<x>-z<y)))"))
#print(CONVERT2("½x(y<x&§y(y<x>½z(y<z&z<x)))"))
#print(CONVERT2("½x§y§z((y<z&z<w)>½w§y(½w((y<z&z<w)&(y<w&w<x))_y=w))"))
#print(LESSCONVERT("﻿∃x(∃y∀z(a→z=y)→∀z(z∈x↔∃x(x∈y∧∀ya)))"))


#searches the start of a string for a value and returns the amount of occurences 
def searcher(x,s):
    xs = 0
    for i in s:
        if i == x:
            xs+=1
        else:
            break
    return xs

atomic_proposition = "atomic_proposition"
individual = "individual"
function = "function"
predicate = "predicate"
counter = "counter"
arity = "arity"
wff = "wff"
term = "term"
input_ = "input"

def prepend(xs,x):
    xs.insert(0,x)

def poor_polish_to_tree(string):
    stack = []
    def parse(s):
        if s == "":
            return
        head = s[0]
        tail = s[1:]
        if head == "¤":
            name = searcher("¤",tail)+1
            tail2 = s[name:]
            #print(tail2)
            counters = searcher("'",tail2[1:])+1
            tail3 = tail2[counters:]
            arityNumber = searcher("*",tail3)
            if name == 1:
                prepend(stack,([atomic_proposition,"¤",[counter,"'"*counters]],0))
                """"g = "A"
                if counters == 2:
                    g = "B"
                if counters == 3:
                    g = "C"
                if counters == 4:
                    g = "D"
                prepend(stack,(g,0))"""
            elif name == 2:
                prepend(stack,([individual,"¤¤",[counter,"'"*counters]],0))
            elif name == 3:
                prepend(stack,([function,"¤¤¤",[counter,"'"*counters],[arity,"*"*arityNumber]],arityNumber))
            elif name == 4:
                prepend(stack,([predicate,"¤¤¤¤",[counter,"'"*counters],[arity,"*"*arityNumber]],arityNumber))
                """"g = "="
                if counters == 2:
                    g = "<"
                prepend(stack,(g,2))"""
            tail = tail3[arityNumber:]
        elif head == "!":
            prepend(stack,("!",1))
        elif head == ">":
            prepend(stack,(">",2))
        elif head == "§":
            prepend(stack,("§",2))
        parse(tail)
    parse(string)
    
    #we simply have a list of inputs back to back, we need to make a tree structure out of them
    def inputParse(xs):
        l = len(xs)
        if l == 1:
            return xs[0]
        end = xs[-1]
        beginning = xs[:-1]
        return [input_,inputParse(beginning),end]
    #print(stack)
    stack3 = []
    for i in stack:
        stack3.append(i[1])
    #print(stack3)
    asd = [1,2]
    asd.pop(0)
    #print(asd[0])
    #now we have a stack with pairs, it's easy to now match em, cause they're in polish order.
    #I need to go through the stack and keep an internal second stack for inputs and that second stack will build up to become the result
    stack2 = []
    for element in stack:
        #print("   ",len(stack2))
        #print(stack2)
        #if stack2 != []:
            #print(stack2[0],stack2[-1])
        arityNumber = element[1]
        if arityNumber == 0:
            prepend(stack2,element[0])
        elif arityNumber == 1:
            stack2[0] = [wff,"!",stack2[0]]
        elif element[0] == ">":
            #print(stack2)
            first = stack2.pop(0)
            stack2[0] = [wff,">",first,stack2[0]]
            #print(stack2)
        elif element[0] == "§":
            first = stack2.pop(0)
            stack2[0] = [wff,"§",first,stack2[0]]
        elif element[0][0] == function:
            inputs = stack2[:arityNumber]
            stack2 = stack2[arityNumber:]
            prepend(stack2,[term,element[0],inputParse(inputs)])
        else:
            inputs = stack2[:arityNumber]
            stack2 = stack2[arityNumber:]
            prepend(stack2,[wff,element[0],inputParse(inputs)])
    print(len(stack2))
    return stack2[0]

print()
#print(poor_polish_to_tree("¤¤¤¤''***¤'¤'¤'"))
print("")


#print(poor_polish_to_tree(">§¤'>¤''¤'''>§¤'¤''§¤'¤'''"))

#print(poor_polish_to_tree(">¤¤¤¤′**¤'¤''>¤¤¤¤′**¤'¤'''¤¤¤¤′**¤''¤'''"))

#print(poor_polish_to_tree(">¤¤¤¤′**¤'¤''>¤¤¤¤''**¤'¤'''¤¤¤¤''**¤''¤'''"))

#print(poor_polish_to_tree(">¤¤¤¤′**¤'¤''>¤¤¤¤''**¤'''¤'¤¤¤¤''**¤'''¤''"))

#print(poor_polish_to_tree(">§¤'!>>¤¤¤¤''**¤'¤''¤¤¤¤''**¤'¤'''!>¤¤¤¤''**¤'¤'''¤¤¤¤''**¤'¤''¤¤¤¤′**¤''¤'''"))

#print(poor_polish_to_tree("!§¤'!>!§¤''!§¤'''>¤''''¤¤¤¤′**¤'''¤''§¤'''!>>¤¤¤¤''**¤'''¤'!§¤'!!>¤¤¤¤''**¤'¤''!§¤''¤''''!>!§¤'!!>¤¤¤¤''**¤'¤''!§¤''¤''''¤¤¤¤''**¤'''¤'"))

#print(poor_polish_to_tree("!§¤'!§¤''>§¤'>¤¤¤¤''**¤'¤''¤¤¤¤''**¤'¤'''¤¤¤¤''**¤''¤'"))

#print(poor_polish_to_tree(">¤¤¤¤''**¤'¤''!§¤'!!>¤¤¤¤''**¤'¤''!§¤'''>¤¤¤¤''**¤'''¤'!¤¤¤¤''**¤'''¤''"))

#print(poor_polish_to_tree("!§¤'!!>¤¤¤¤''**¤''¤'!§¤''>¤¤¤¤''**¤''¤'!§¤'''!!>¤¤¤¤''**¤''¤'''!¤¤¤¤''**¤'''¤'"))

#print(poor_polish_to_tree("!§¤'!§¤''§¤'''>!>¤¤¤¤''**¤''¤'''!¤¤¤¤''**¤'''¤''''!§¤''''!§¤''!>>!§¤''''!!>!>¤¤¤¤''**¤''¤'''!¤¤¤¤''**¤'''¤''''!!>¤¤¤¤''**¤''¤''''!¤¤¤¤''**¤''''¤'¤¤¤¤′**¤''¤''''!>¤¤¤¤′**¤''¤''''!§¤''''!!>!>¤¤¤¤''**¤''¤'''!¤¤¤¤''**¤'''¤''''!!>¤¤¤¤''**¤''¤''''!¤¤¤¤''**¤''''¤'"))




def convert_from_polish(string):
    #should we parse from the end?
    #what do formulas end in?
    #well, atomic propositions in wffs. individuals in fulfilled predicates. that's all there is to end in
    #we should find the last arrow or quantifier?
    if string[-1] in INDIVIDUALSYMBOLS:
        return 2
    
    
    if string[0] == ">":
        return 2
    
    position = ranking(string)[0]
    rank = 2
    if rank < 0:
        return CONVERT(string[1:-1])
    elif rank == 0:
        if ATOMICPROPOSITIONSYMBOL(string[0]) or INDIVIDUALSYMBOL(string[0]):
            return (string[0],string[1:])
        elif FUNCTIONSYMBOL(string[0]) or PREDICATESYMBOL(string[0]):
            one = string[:string.find("(")]
            two = string[string.find("("):][1:-1]
            counter = one.count("′")*"′"
            if "#" in one:
                counter = one[1:one.find("#")] 
            arity = one[max(one.find("′")+one.count("′"),one.find("#")+1,1):]
            try:
                arity = int(arity)
            except:
                arity = 1
            a = ""
            parenthesis = 0
            for i in two:
                if i == "(":
                    parenthesis += 1
                    a += "("
                elif i == ")":
                    parenthesis -= 1
                    a += ")"
                elif parenthesis == 0 and i == ",":
                    a += "."
                else:
                    a += i
            return ((one[0],counter,arity),[CONVERT(i) for i in a.split(".")])
    elif rank == 2 and position == 0:
        return (string[0],CONVERT(string[1:]))
    elif rank == 1 and position == 0:
        one = string.find("(")
        for i in range(1,string.find("(")):
            if string[i] in ["∀","∃"]:
                one = i
                break
        return (string[0],CONVERT(string[1:one]),CONVERT(string[one:]))
    elif rank >= 1:
        return (CONVERT(string[:position]),string[position],CONVERT(string[1+position:]))

depolish = 2

#testing this for the translation to the simpler 4000 character system of mine
print(polisher(REWRITE(CONVERT("∃𝒙∀𝒚∃𝒛∀𝒘((𝒙∈𝒗∧(𝒚∈𝒙→𝒛∈𝒗∧¬𝒙=𝒛∧𝒚∈𝒛))∨(¬𝒙∈𝒗∧(𝒚∈𝒗→𝒛∈𝒚∧𝒛∈𝒙∧(𝒘∈𝒚∧𝒘∈𝒙→𝒘=𝒛))))"))))
print(polisher(CONVERT(LESSCONVERT("P1(x)>Q'2(x,y)>R2#3(x,y,z)>S1(F(x,y,z))"))))
while True:
    if input("make a proof? ") == "yes":
        a = """"""
        while True:
            print(a)
            b = input("give a line in a proof or the empty string to exit the proof or \"finish\" to finish the proof ")
            if b == "":
                break
            elif b == "finish":
                a = a[:-1]
                c = STABLEPROOF(PROOFCONVERT(a))
                print(c)
                if c:
                    print(LESSCONVERT(a.split(".")[-1]))
                break
            else:
                a += b+"\n"
    elif input("show theorems? ") == "yes":
        laconize(THEOREMS)
    elif input("polish? ") == "yes":
        print(polisher(CONVERT(LESSCONVERT(input("")))))
    elif input("make into tree? ") == "yes":
        print(CONVERT(LESSCONVERT(input(""))))
    elif input("exit? ") == "yes":
        break
