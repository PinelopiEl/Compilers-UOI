#Athanasia-Tsaousi Danai 3349 cs03349
#Eleftheriadi Pinelopi 3221 cs03221

#imports
import os
import sys
import string

#vars for lexixal analizer
lineNo=0#counter for lines
i=0 #counter for chars

#keywords (lists)
keywords = ["program", "declare", "if", "else", "while", "switchcase", "forcase", "incase", "case", "default", "not", "and", "or", "function", "procedure", "call", "return","in","inout","input","print"]
stats = [ "if", "while", "switchcase", "forcase", "incase","return","call","print","input"]
oper = ["=","<=",">=",">","<","<>"]
symbols=["+","-","/","*"]
punc = [".",",",";"]
paren=["{","}","[","]","(",")"]

#globals
global inputFile
global line
global token
global ch
global relop
global progName
global tempvars
global name

#variables (flags,counters etc.)
id_array = [] #for ID()
functionFlag = 0 #fuction existence
qline = 0 #etiketa quad
quadsList = []
tcount = 0
tempvars = []
stack = []
head =0
llist=[] #backpatch
l=""
labelZero=True
infile = "" #for .init file
entered = 0
name=""         #gia subprogram
scopeName=[]
scopesList = list()
mipsfile = "" #for assembly file
actualList = []
progFramelength = -1 #telikos
asmfile=""
mainLabel =""
scopeFile = ""
insideMainFlag=False

################ TOKEN ####################################
class Token:

    def __init__(self, tokenType, tokenString, lineNo):
        self.tokenType =tokenType
        self.tokenString = tokenString
        self.lineNo = lineNo

    def getEntType(self):
         return self.tokenType
         
    def setType(self,tokenType):
         self.tokenType = tokenType

    def getString(self):
         return self.tokenString
         
    def setString(self,tokenString):
         self.tokenString = tokenString
         
    def getLine(self):
         return self.lineNo
         
    def setLine(self,lineNo):
         self.lineNo = lineNo
         
########### Input file ####################################
namefile = sys.argv[1]
inputFile = open(namefile,"r")



########################################################### 
################ LEX ###################################### 
########################################################### 

#otan kaleite tha epistrefei thn epomenh lektiki monada
def lex1():
    global lineNo,i
    global inputFile
    global token
    global ch,charbuff2
    while(True):
        
        #read character by character
        ch=inputFile.read(1)
        i = 1; # next character
        #check leukous xaraktires (space,tab,empty line)
        while ch=="\n" or ch==" " or ch=="\t":
            if ch=="\n":
                i=0
                lineNo += 1
                
            ch=inputFile.read(1)
            
            i+=1

       
        #store each char in a buffer
        charbuff=ch
        if ch == "#" :
            ch=inputFile.read(1)
            while ch != "#":
                ch=inputFile.read(1)
           
        
        if ch == "+" or ch == "-":
            token=Token("addOperator",ch,lineNo)
            return token
            break
        
        if ch.isdigit():
            check=0             
            x = 2^32 - 1 
            number = ""
            number+=ch
            ch =inputFile.read(1)
            if not ch.isdigit():
                inputFile.seek(inputFile.tell()-1)
                token=Token("number",number,lineNo)
                return token
                check=1
            while ch.isdigit() and check==0:
                number += ch
                ch = inputFile.read(1)
                if not ch.isdigit():
                    inputFile.seek(inputFile.tell()-1)
           
               
            if -x < int(number) < x and check==0:
                token=Token("number",number,lineNo)
                return token
            else: #ERROR
                print("ERROR! The number isn't inside the proper boundaries")
                exit(1)
            break
        if ch.isalpha():
            check=0
            word=""
            word += ch
            ch = inputFile.read(1)
            if not ch.isalpha() and not ch.isdigit():
                inputFile.seek(inputFile.tell()-1)
                token=Token("identifier",word,lineNo)
                return token
                check=1
            while (ch.isalpha() or ch.isdigit()) and check==0:
                word += ch
                ch = inputFile.read(1)
                if not ch.isalpha() and not ch.isdigit():
                    inputFile.seek(inputFile.tell()-1)
            if word in keywords:
                token=Token("keyword",word,lineNo)
                return token
            else:
                if len(word) > 30:
                    print("ERROR!Word too big!")
                    exit(1)
                if(check==0):
                    token=Token("identifier",word,lineNo)
                    return token

            break        
            
        if ch == "*" or ch == "/":
            token=Token("mulOperator",ch,lineNo)
            return token
            break    
        if ch == "(" or ch == "{" or ch == "[" or ch == ")" or ch == "}" or ch == "]":
            token=Token("groupSymbol",ch,lineNo)
            return token
            break   

        if ch in punc:
            token=Token("delimiter",ch,lineNo)
            return token
            break    
        if ch == ":":
            ch = inputFile.read(1)
            if(ch == "="):
                token=Token("assignment",":=",lineNo)
                return token
            else: 
                #ERROR
                print("The character : MUST be followed by =")
                exit(1)
            break        
        if ch == "<":
            charbuff=ch
            ch = inputFile.read(1)
            if ch == "=" or ch == ">":
                token=Token("relOperator", charbuff+ch ,lineNo)
                return token
            else:
                inputFile.seek(inputFile.tell()-1)
                token=Token("relOperator", charbuff,lineNo)
                return token
            break        
        if ch == ">":
            charbuff=ch
            ch= inputFile.read(1)
            if(ch == "="):
                token=Token("relOperator", charbuff+ch ,lineNo)
                return token
            
            else:
                inputFile.seek(inputFile.tell()-1)
                token=Token("relOperator", charbuff ,lineNo)
                return token
            break    
        if ch == "=":
            token=Token("relOperator", ch ,lineNo)
            return token
            break

        if ch == ".":
            token=Token("end",".",lineNo)
            return token
            break
   
###########################################################         
############## SYNTAX #####################################
###########################################################

def program(): #anagnwrizei id kai kalei ypoloipes synarthseis
    global token, functionFlag ,progName, scopeName,name


    if token.getString()  == "program":
        token = lex1()
        if token.getEntType() == "identifier":
        
            ID(token.getString())
            progName = token.getString()
            
            #prosthiki neou scope
            addSc()
            
            token = lex1()
            block()
            
            genQ("halt","_","_","_")
            genQ("end_block",progName,"_","_")
            
            makeNewFrl(name, scopesList[-1].get_current_offset())
            #dimiourgia arxeiou assembly
            makeAssembly(namefile[:-3])
            makeScopeFile()
            scopesList.pop()
            
            token = lex1() #gia na parw tin teleia "."
            
            if token.getString()  == ".":
                inputFile.close()
            
                print("END OF FILE!")
                if functionFlag == 1:#exei function
                    intFile(namefile[:-3])
                else:
                    newCFile(namefile[:-3])
                    makeCcode()
          
                exit(1)
        else:#ERROR
            print("ERROR!Den vrethike id gia to program!")
            exit(1)

        
            

    else:#ERROR
        print("ERROR!No program found!")
        exit(1)
        
def block():
    global token,progName,functionFlag,entered,name

    declarations()
    subprograms()
    if entered==0:

        genQ("begin_block",progName,"_","_")
    entered=0
    
    statements()
    
def declarations(): 
    global token
    
    while token.getString() == "declare":
        token = lex1()
        varlist()
        
        if token.getString() == ";":
            token = lex1()
            
        else:#ERROR
            print("ERROR! ; not found!",lineNo,token.getString())
            exit(1)
    return  
    
def varlist():
        global token ,tempvars
       
        if token.getEntType() == "identifier":
            addVarEnt(token.getString())
            tempvars.append(token.getString())
            ID(token.getString())
            token = lex1()
            while token.getString() == ',':
                token = lex1()
                if token.getEntType() == "identifier":
                   addVarEnt(token.getString()) 
                   tempvars.append(token.getString())
                   ID(token.getString())
                   token = lex1()
                else:
                    print("ERROR!After comma excepted ID!")
                    exit(1)
        else:
            return
 
def subprograms():  
    global token,functionFlag,entered
    while token.getString()=="function" or token.getString()=="procedure":
        addSc()
        functionFlag = 1
        entered=1
        token=lex1()
        subprogram()

    
    return

def subprogram():
        global token, progName, name
        
        beginWrite = False
        if token.getEntType() == "identifier":
            id = token.getString
            name=token.getString()
            ID(token.getString())
            addFuncEnt(id)
            token=lex1()
            if token.getString() == "(":
                token=lex1()
                formalparlist()
                
                if token.getString() != ")":
                    print("ERROR,expected )!Subprogram",lineNo)
                    exit(1)
            
                else:
                    nextQuad()
                    startQ = makeNewStartQ(name)
                    genQ("begin_block",name,"_","_")
                    token=lex1()
                    block()
                if name not in stats:
                    genQ("end_block",name,"_","_")
                    
                    
                token = lex1()
            else:#ERROR
                print("ERROR!Den vrethike ( ")
                exit(1)
        else:#ERROR
            print("ERROR!Den vrethike id gia to ")
            exit(1)
    
def formalparlist():
        global token
        if token.getString() != "in" and token.getString() != "inout":
            return
        formalparitem()
        while token.getString() == ",":
            token=lex1()
            formalparitem()
              
def formalparitem():
        global token
       
        if token.getString() == "in" or token.getString() == "inout":
            parMode = token.getString()
            token=lex1()
            if token.getEntType() != "identifier":
                print("ERROR!Expected id after in/inout")
                exit(1)
            p = token.getString()
            ID(token.getString())
            addArg(parMode)
            addParamEnt(p, parMode)
            token=lex1()
         
        else:
            print("ERROR!Must have in or inout!")
            
def statements():
    global token,name
    if token.getString() == "{":
        token=lex1()
        while token.getString() != "}":
            S = statement()
            while token.getString() == ";":
                token=lex1()
                statement()
            return S
       
    else:
        S = statement()
        token = lex1()
        if token.getString() != ";"and name in stats :
            print("Error!Eprepe na exei erwtimatiko to statement")
        return S
          
def statement():    
        global token
        id=""
        if token.getEntType()=="identifier":
            ID(token.getString())
            idname=token.getString()
            token =lex1()
            if token.getString() == ":=":
                a=assignStat()
                genQ(":=",a,"_",idname)
                
        elif token.getString() == "if":
            token=lex1()
            ifStat()
        elif token.getString() == "while":
            token=lex1()
            whileStat()
        elif token.getString() == "switchcase":
            token=lex1()
            switchcaseStat()
        elif token.getString() == "forcase":
            token=lex1()
            forcaseStat()
        elif token.getString() == "incase":
            token=lex1()
            incaseStat()
        elif token.getString() == "call":
            token=lex1()
            callStat()
        elif token.getString() == "return":
            token=lex1()
            returnStat()
        elif token.getString() == "input":
            token=lex1()
            inputStat()
        elif token.getString() == "print":
            token=lex1()
            printStat()
            
def assignStat():
        global token
        token = lex1()      
        prev=token.getString()
        a = expression()
        if a == None:
            return prev 
        else:
            return a
          
def ifStat():
    
        global token 
        if token.getString() == "(":
            token=lex1()
            C = condition()
            CTrue = C[0]
            CFalse = C[1]
            if token.getString() != ")":
                print("ERROR,expected )!")
                exit(1)
            
            else:
                token=lex1()
                backpatch(CTrue,nextQuad())
                statements()
                
                iflist = createlist(nextQuad())
                genQ("jump","_","_","_")
                backpatch(CFalse,nextQuad())
                
                elsepart()
                backpatch(iflist,nextQuad())
        else:
            print("ERROR,expected ( for if")
            exit(1)
            
def elsepart():
    
        global token
        token=lex1()
        if token.getString() != "else":
            return
        else:
             token=lex1()
             statements()
             token=lex1()

def whileStat():
        global token
        Bq = nextQuad()
        if token.getString() == "(":
            token=lex1()
            C = condition()
            CTrue = C[0]
            CFalse = C[1]
            
            if token.getString() != ")":
                print("ERROR,expected )!")
                exit(1)
            
            else:
                token=lex1()
                backpatch(CTrue,nextQuad())
                statements()
                token = lex1()
                genQ("jump","_","_",str(Bq))
                backpatch(CFalse,nextQuad())
                
        else:
            print("ERROR,expected (  in WHILE")
            exit(1)
            
def switchcaseStat():
        global token
        exitlist = emptylist()
        
        while token.getString() == "case":
            token = lex1()
            if   token.getString() == "(":
                token = lex1()
                C = condition()
                CTrue = C[0]
                CFalse = C[1]
                
                if token.getString() != ")":
                    print("ERROR,expected )!")
                    exit(1)
                else:
                    backpatch(CTrue,nextQuad())
                    token=lex1()
                    statements() 
                    
                    e = createlist(nextQuad())
                    genQ("jump","_","_","_")
                    mergelist(exitlist,e)
                    backpatch(CFalse,nextQuad())
                    token = lex1()
                    
            else:
                print("ERROR!Expected (")
                exit(1)
                
        if token.getString() == "default":
            token = lex1()
            statements()
            backpatch(exitlist,nextQuad())
        else:
            print("ERROR!Expected default!")
            exit(1)

def forcaseStat():
        global token
        if token.getString() == "case":
            p1Quad = nextQuad()
            token=lex1()
            if token.getString() == "(":
                token=lex1()
                C = condition()
                CTrue = C[0]
                CFalse= C[1]
                if token.getString() != ")":
                    print("ERROR,expected )!")
                    exit(1)
            
                else:
                    backpatch(CTrue,nextQuad())
                    token=lex1()
                    statements()
                    genQ("jump","_","_",str(p1Quad))
                    backpatch(CFalse,nextQuad())
                    if token.getString() == "default":
                        token=lex1()
                        statements()
                    else:
                        print("ERROR,expected default!")
                        exit(1)
            else:
                print("ERROR,expected (!FORCASE")
                exit(1)
        
        else:
            print("ERROR,expected case !")
            exit(1)
    
def incaseStat():
        global token
        w = newtemp()
        p1Quad = nextQuad()
        genQ(":=",1,"_",w)
        if token.getString() == "case":
            token=lex1()
            if token.getString() == "(":
                token=lex1()
                C = condition()
                CTrue = C[0]
                CFalse = C[1]
                if token.getString() != ")":
                    print("ERROR,expected )!")
                    exit(1)
            
                else:
                    backpatch(CTrue,nextQuad())
                    genQ(":=",0,"_",w)
                    token=lex1()
                    statements()
                    backpatch(CFalse,nextQuad())
            else:
                print("ERROR,expected ( !INCASE")
                exit(1)
        
        else:
            print("ERROR,expected case !")
            exit(1)
        genQ("=",w,0,p1Quad)
    
def callStat():
        global token
       
        if token.getEntType()=="identifier":
            id=token.getString()
            ID(token.getString())
            token=lex1()
            
            if token.getString() == "(":
                actualparlist() 
                w = newtemp()
                genQ("par",w,"RET","_")   
            if token.getString() != ")":
                print("ERROR,expected )!Call stat")
                exit(1)
            else:
                genQ("call",id,"_","_")
                token=lex1()
        
        else:
            print("ERROR,expected ( in CALL STAT")
            exit(1)
            
def returnStat():
        global token
        if token.getString() == "(":
            token=lex1()
            Ex = expression()
            if token.getString() != ")":
                print("ERROR,expected )!RETURN")
                exit(1)
            genQ("retv",Ex,"_","_")
            token=lex1()
        
        else:
            print("ERROR,expected (!RETURN")
            exit(1)
    
def inputStat():
        global token
        if token.getString() == "(":
            token=lex1()
            if token.getEntType()!="identifier":
                print("ERROR,expected ID !")
                exit(1)
            inp =token.getString()
            id = ID(token.getString())
            genQ("inp",inp,"_","_")
            token = lex1()
            if token.getString() != ")":
                print("ERROR,expected )!")
                exit(1)
        
            token = lex1()
        else:
            print("ERROR,expected ( !INPUTSTAT")
            exit(1)

def printStat():
        global token
        if token.getString() == "(":
            token=lex1()
            E = expression()
            genQ("out",E,"_","_")
            if token.getString() != ")":
                print("ERROR,expected )!")
                exit(1)
            token=lex1()
        
        else:
            print("ERROR,expected (!PRINT")
            exit(1)
            
def condition():
        global token
        BOOL = boolterm()
        CTrue = BOOL[0]
        CFalse = BOOL[1]
        while(1):
            if token.getString() == "or":
            
                token=lex1()
                backpatch(CFalse,nextQuad())
            
                BOOL2 = boolterm()
            
                BOOL2True = BOOL2[0]
                BOOL2False = BOOL2[1]
            
                CTrue = mergelist(CTrue,BOOL2True)
                CFalse=BOOL2False
            else:
                C = [CTrue,CFalse]
                return C

def boolterm():#AND
        global token
        B = boolfactor()
        BOOLTrue = B[0]
        BOOLFalse = B[1]
        while(1):
            if token.getString() == "and":
                token = lex1()
                backpatch(BOOLTrue,nextQuad())
            
                B2 = boolfactor()
                B2True = B2[0]
                B2False = B2[1]
                BOOLFalse = mergelist(BOOLFalse,B2False)
                BOOLTrue = B2True
            else:
                BOOL = [BOOLTrue,BOOLFalse]
                return BOOL
        
def boolfactor():#NOT
        global token
        if token.getString() == "not" :
            token = lex1()
            if token.getString() == "[":
                token = lex1()
                C = condition()
                if token.getString() != "]":
                    print("ERROR!]")
                    exit(1)
                else:
                    token = lex1()
                    BTrue = C[0]
                    BFalse = C[1]
                    B = [BTrue,BFalse]
                    return B
            else:
                print("ERROR!")
        elif token.getString() == "[":
                token = lex1()
                B = condition()
                if token.getString() != "]":
                    print("ERROR!]")
                    exit(1)  
                else:
                    token = lex1()
                    return B
        else:
            E1 = expression()
            r = REL_OP()
            E2 = expression()
            BTrue =createlist(nextQuad())
            genQ(r,E1,E2,"_")
            BFalse = createlist(nextQuad())
            genQ("jump","_","_","_")
            B = [BTrue,BFalse]
            return B
            
def expression():
        global token 
        mys = token.getString()
        opt = optionalSign()
        T1 = term()
        if opt!=None:
            signt = newtemp()
            genQ(mys,"_",T1,signt)
            T1 = signt
        
        while token.getEntType() == "addOperator":
            oper = token.getString()
            
            ADD_OP()
            T2 = term()
            w = newtemp()
            genQ(oper,T1,T2,w)
            T1=w
        
        return T1
        
                         
def term():#an einai * h /
        global token 
        F1 = factor()
        while(1):
            if token.getEntType() == "mulOperator":
                oper = token.getString()
                MUL_OP()
                F2 = factor()
                w = newtemp()
                genQ(oper,F1,F2,w)
                F1 = w
            else:
                return F1
    
def factor():#syntelestes
        global token 
        if token.getEntType() == "number":
            return INTEGER()
        elif token.getString() == "(":
            token = lex1()
            Ex = expression()
            if token.getString() == ")":
                token = lex1()
                return Ex
            else:
                print("ERROR!Expected ) to close FACTOR")
                exit(1)
        elif token.getEntType() == "identifier":
            mytoken=token.getString()
            ID(token.getString())
            myid=idtail()
            if myid==None:
                return mytoken
            else:
                return myid
            
def idtail():
        global token , act
        funcname = token.getString()
        token = lex1()
        if token.getString() == "(":
            act = actualparlist()
            w = newtemp()
            genQ("par",w,"RET","_")
            genQ("call",funcname,"_","_")
            token = lex1()
            
            if token.getString() == ")":
                  return act
            
        else:
            return 
            
def actualparlist(): #is a list of parameters
        global token
        token = lex1()
        actualparitem()
        
        while token.getString() == ",":
            token=lex1()
            actualparitem()
    
def actualparitem():
        global token
       
        if token.getString() == "in":
            token=lex1()
            mytoken = token.getString()
            e = expression()
            genQ("par",e,"CV","_")
            
            return mytoken
       
        elif token.getString() == "inout":
            token=lex1()
            mytoken2 = token.getString()
            if token.getEntType() != "identifier":
                print("ERROR!")
                exit(1)
                
            ID(token.getString())
            genQ("par",token.getString(),"REF","_")
            token=lex1()
            return mytoken2
        else:
            print("ERROR!Must have in or inout!")  
            
def optionalSign():#an einai + h -
        global token 
        sign = token.getString()
        if token.getEntType() == "addOperator":
            ADD_OP()
            return sign
        else:
            return
  
def REL_OP():
        global token
        reop = token.getString()
        if token.getString() not in oper:
            print("ERROR!Expected operator!")
            exit(1)
        token = lex1()
        return reop
  
def ADD_OP():
        global token 
        addop = token.getString()
        if token.getEntType() != "addOperator":
            print("ERROR!Expected + or -")
            exit(1)
        token = lex1()
        return addop

def MUL_OP():
        global token 
        mulop = token.getString()
        if token.getEntType() != "mulOperator" :
            print("ERROR!Expected * or \\")
            exit(1)
        token = lex1()
        return mulop
       
def INTEGER():
        global token 
        integer = token.getString()
        if isinstance(int(token.getString()) ,int) == False:
            print("ERROR!Expected integer!")
            exit(1)
        token=lex1()
        
        return integer
      
def ID(s):
        global token
        word_list = []
        st=str(s)
       
        id_array.append(st)
        i=0
        j=0
        for i in range(0, len(st)):
            word_list.append(st[i])
            i+=1
        
        if word_list[j].isalpha() != True:
            print("ERROR!Must start with letter!")
            exit(0)


########################################################################################
#######################      ENDIAMESOS KWDIKAS        #################################
########################################################################################

# returns the the number of the next line(quad)
def nextQuad():
    global qline
    return qline+1 #next label
  
#creates the next quad
def genQ(op,x,y,z):
    global qline
    global quadsList
    form = ""
    qline += 1
    form = (str(op) + " " + str(x) + " " + str(y) + " " +str(z) +"\n")
    quadsList.append(form)
   
    print(form)   
        
#nea prosorini metablhth, morfhs T_1,T_2...
def newtemp():
    global tcount,tempvars
    tcount+=1
    newT = "T_{0}".format(tcount) #to format analoga thn timh toy count tha allazei thn timh mesa sta {}
    tempvars.append(newT)
    
    offset = scopesList[-1].get_current_offset_advanced()
    scopesList[-1].add_Entity(TempVariable(newT,offset))

    return newT
   
#adeia lista etiketon tetradon
def emptylist():
    em = []
    return em
    
#lista etiketon tetradon me pedio x
def createlist(qLine):
    n = []
    n.append(qLine)
    return n
  

def mergelist(list1,list2):
    return list1+list2
    
def backpatch(list,ql):
    global quadsList,llist
    for k in list:
        l=quadsList[k-1] #line to update with the ql(=label)
        line_parts=l.split()
        line_parts[3]=str(ql)
        
        l= line_parts[0]+ " "+line_parts[1]+" " +line_parts[2]+" "+line_parts[3]+"\n"
        quadsList[k-1]=l
    
#############################################
############ C FILE #########################
#############################################
def intFile(infilename):
    global infile
    f = infilename + ".int"
    infile = open(f ,"w")
    for q in quadsList:
        infile.write(q + '\n')
    infile.close()

def newCFile(name):
    global cfile
    n = name + ".c"
    cfile = open(n,"w+")
    
def makeCcode():
    global code,tempvars,labelZero
    mydeclare= ""
    codeline=""
    comment=""
    code = []
    #create main code
    code.append("#include <stdio.h> \n\n")
    code.append("int main(){")
    code.append("\n")
    indexOfDeclare=code.index("\n")
    for qu in quadsList:

        q=qu.split()
        comment="//("+ q[0]+", " + q[1]+", "+ q[2]+", "+ q[3]+ ")\n"
        
        if q[0] == "begin_block":
            if q[1] == progName:
                if tempvars:
                    intbuf = "\n\tint\t"
                    for t in tempvars:
                        intbuf += t+","
                    mydeclare = intbuf[:-1] + ";" + "\n"
                    code.append(intbuf[:-1] + ";" + "\n")
                    if labelZero==True:
                        code.append("\t"+"L_0:"+"\n")
                        labelZero==False
             
        elif q[0] == "end_block" and q[1] == progName:
            code.append("}")
        elif q[0] == "halt":
            code.append("\t"+ "L_" + str(quadsList.index(qu))+ ": \n ")
        elif q[0] in oper:
            if q[0] == "=":
                q[0] = "=="
            elif q[0] == "<>":
                q[0] = "!="
            code.append("\t"+"L_"+ str(quadsList.index(qu))+" : "+"if (" + q[1] + q[0] +q[2]+ ") " +"goto L_"+q[3]+";"+comment)
        elif q[0] in symbols:
            code.append("\t"+"L_"+ str(quadsList.index(qu))+" : "+ q[3] + "=" + q[1] + q[0] +q[2]+";"+comment)
        elif q[0] == ":=":
            code.append("\t"+"L_"+ str(quadsList.index(qu))+" : "+ q[3] + "=" + q[1]+";"+ " "+ comment)
        elif q[0] == "jump":
            code.append("\t"+"L_"+ str(quadsList.index(qu))+" : "+"goto L_"+q[3] + ";" +comment)
        elif q[0] == "out":
            code.append("\t"+"L_"+ str(quadsList.index(qu))+" : "+"printf" + '("%d\\n", ' + q[1] + ");" + comment) 
        elif q[0] == "inp":
            code.append("\t"+"L_"+ str(quadsList.index(qu))+" : "+"scanf" + '("%d", ' + '&' + q[1] +");" + comment) 
        elif q[0] == "retv":
            code.append("\t"+"L_"+ str(quadsList.index(qu))+" : "+ "return (" + q[1] +");" + comment)
        
   
    for codeline in code:
        cfile.write(codeline)
        
############################################################################
############################  SYMBOL TABLE  ################################
############################################################################


#CLASSES SYMBOL TABLE
#######################################
class Entity:
    def __init__(self,name,type):
        self.name = name
        self.type = type
    
    def getName(self):
        return self.name
        
    def getEntType(self):
        return self.type
        
class varEn(Entity):

    def _init_(self,name,type,offset):
        super().__init__(name,"Variable")
        self.offset = offset
        
    def getOffset(self):
        return self.offset
    
    def setOffset(self,offset):
        self.offset = offset
        
class Function(Entity):

    def __init__(self, name, startQ=-1):
        super().__init__(name, "Function")
        self.__startQ = startQ
        self.__arguments_list = list()
        self.__framelength = -1

    def getStartQ(self):
        return self.__startQ

    def setStartQ(self, start_quad):
        self.__startQ = start_quad

    def getArgumList(self):
        return self.__arguments_list

    def addArgum_inList(self, argument):
        self.__arguments_list.append(argument)

    def getFramelength(self):
        return self.__framelength

    def setFramelength(self, framelength):
        self.__framelength = framelength
        
class Const(Entity):
    def __init__(self, name, value):
        super().__init__(name, "Constant")
        self.value = value
        
    def get_value(self):
        return self.value
        
    def set_value(self, value):
        self.value = value
        
class Parameter(Entity):
    def __init__(self, name, parMode, offset=-1):
        super().__init__(name, "Parameter")
        self.parMode = parMode
        self.offset = offset

    def getParMode(self):
        return self.parMode

    def setParMode(self, parMode):
        self.parMode = parMode

    def getOffset(self):
        return self.offset

    def setOffset(self, offset):
        self.offset = offset
    

class TempVariable(Entity):
    def __init__(self, name, offset=-1):
        super().__init__(name, "Tempvar")
        self.offset = offset

    def getOffset(self):
        return self.offset

    def setOffset(self, offset):
        self.offset = offset        
        
class Scope:
    def __init__(self, nestLevel=0, enclosing_scope=None):
        self.__entList = list()
        self.__nestLevel = nestLevel
        self.__current_offset = 12
        self.__enclosing_scope = enclosing_scope

    def get_entList(self):
        return self.__entList

    def add_Entity(self, Entity):
        self.__entList.append(Entity)

    def get_nestLevel(self):
        return self.__nestLevel

    def get_current_offset(self):
        return self.__current_offset

    def get_current_offset_advanced(self):
        current = self.__current_offset
        self.__current_offset += 4  # this is the next offset
        return current

    def get_enclosing_scope(self):
        return self.__enclosing_scope
  
        
class Argument:
    def __init__(self, parMode,nextArgument=None):
        self.parMode = parMode
        self.nextArgument = nextArgument

    def getParMode(self):
        return self.parMode

    def setParMode(self, parMode):
        self.parMode = parMode
    
    def getNextArgum(self):
        return self.nextArgument

    def setNextArgum(self, nextArgument):
        self.nextArgument = nextArgument        
        
###########################################################################
################  FUNCTIONS SYMBOL TABLE  #################################
###########################################################################

#elegxei an exei hdh dilothi entity me idio name,type kai nestingLevel
def alreadyDefined(name,type,nestLevel):
    retVal= False
    sc = scopesList[nestLevel]
    entl = sc.get_entList()
    for e in range(len(entl)):
        curentity = sc.get_entList()[e]
        if curentity.getName() == name and curentity.getEntType()== type:
            retVal=True
            return retVal
    return retVal
    
#elegxei an exei hdh dilothi entity me idio name kai nestingLevel os parameter entity
def checkVarParam(name, nestLevel):                  
    elems = scopesList[nestLevel].get_entList()
    for e in range(len(elems)):
        if elems[e].getEntType() == "Parameter" and elems[e].getName() == name:
            return True
    return False   
    
#briskei entity me name = entName
def findEnt(entName):
    if len(scopesList)==0:
        return 
    tempsc = scopesList[-1]
    while tempsc != None:       
        for ent in tempsc.get_entList():
            if ent.getName() == entName:
                return ent
        tempsc = tempsc.get_enclosing_scope()    
        
 #getter gia to bathos foliasmatos gia entity me entName
def getEntNestingLevel(entName):
    if len(scopesList)==0:
        return 
    tempsc = scopesList[-1]
    while tempsc is not None:       
        for ent in tempsc.get_entList():
            if ent.getName() == entName:
                return tempsc.get_nestLevel()
        tempsc = tempsc.get_enclosing_scope()   
        
#briskei entity me name = entName kai to sygkekrimeno type
def findEntByType(entName,type):
    if len(scopesList)==0:
        return 
    tempsc = scopesList[-1]
   
    while tempsc != None:        
        for ent in tempsc.get_entList():
            if ent.getEntType()==type and ent.getName() == entName:
                return ent, tempsc.get_nestLevel()
        tempsc = tempsc.get_enclosing_scope()
   
#bazei kainourgio scope sthn scopesList 
def addSc():
    if len(scopesList)==0:
        tempsc = Scope()
        scopesList.append(tempsc)
        return
    enclosing_scope = scopesList[-1]
    tempsc = Scope(enclosing_scope.get_nestLevel() +1, enclosing_scope)
    scopesList.append(tempsc)
    
        
#bazei kainourgio function entity stin scopesList        
def addFuncEnt(id):
    nestLevel = scopesList[-1].get_enclosing_scope().get_nestLevel()
    if alreadyDefined(id,"Function", nestLevel):
        print("ERROR IN addFuncEnt!")
    scopesList[-2].add_Entity(Function(id))

 #bazei kainourgio parameter entity stin scopesList     
def addParamEnt(name,parmode):
    nestL = scopesList[-1].get_nestLevel()
    par_offset = scopesList[-1].get_current_offset_advanced()
    if alreadyDefined(name, "Parameter", nestL):
        print("ERROR!The parameter entity is already defined (addParamEnt())!")
    scopesList[-1].add_Entity(Parameter(name, parmode, par_offset)) 

#bazei kainourgio argument sthn scopesList    
def addArg(parMode):
    if parMode == "in":
        new = Argument("CV")
    else:
        new = Argument("REF")

    scopesList[-2].get_entList()[-1].addArgum_inList(new)
    a = scopesList[-2].get_entList()[-1].getArgumList()
    if len(a) >= 2:
        a[-2].setNextArgum(new)
        
        
#bazei kainourgio variable entity sthn scopesList      
def addVarEnt(name):
    nestL = scopesList[-1].get_nestLevel()
    var_offset = scopesList[-1].get_current_offset_advanced()
    if alreadyDefined(name, "Variable", nestL):
        print("ERROR!The varaiable entity is already defined (addVarEnt())!")
    if checkVarParam(name, nestL):
        print("Error!Its already defined")
    scopesList[-1].add_Entity(varEn(name, var_offset))

#neo framelength se ena function entity
def makeNewFrl(name, framelength):
    global progFramelength, progName
    if name == progName:
        progFramelength = framelength
        return
        
    try:
        index=(scopesList[-2].get_entList()).index(scopesList[-2].get_entList()[-1])
        if index>=0 and index<len(scopesList[-2].get_entList()):
            scopesList[-2].get_entList()[-1].setFramelength(framelength)
    except IndexError:
        return
    
#nea etiketa tetradas se ena function entity 
def makeNewStartQ(name):
    global progName, mainLabel
    startQ = nextQuad()
    if name == progName:
        mainLabel = startQ
        return startQ
    scopesList[-2].get_entList()[-1].setStartQ(startQ)
    return startQ
    
#to arxeio me to scope    
def makeScopeFile():
    scname = "scopeFile.txt"
    scopeFile = open(scname ,"w")
    for s in scopesList:
        scopeFile.write(str(s.__dict__)+"\n")
    scopeFile.close()
    
############################################################################
#################### TELIKOS KWDIKAS #######################################
############################################################################
def gnvlcode(v): 
    entload = findEnt(v)
    nestingLevel = scopesList[-1].get_nestLevel()
    entNestingL = getEntNestingLevel(entLoad.getName())
    mipsfile.write("lw $t0, -4($sp)\n")
    
    level = nestingLevel - entNestingL -1
    while level > 0:
        mipsfile.write("lw $t0, -4($t0)\n")
        level -= 1
    mipsfile.write("addi $t0, $t0,-",entload.getOffset(),"\n")
    
def loadvr(v, r): #metafora dedomenwn ston kataxwriti r 
    mystr = str(v)
    if mystr.isdigit():
        mipsfile.write("li $t"+ r +","+ v +"\n")
    else:
        loadEntity = findEnt(v)
        #h findEnt() epistrefei none otan to entList einai adeio
        if loadEntity == None:
            return
        nestingLevel = scopesList[-1].get_nestLevel()
        entNestingL = getEntNestingLevel(loadEntity.getName())
        if loadEntity.getEntType == "Variable" and entNestingL == 0:
            mipsfile.write("lw    $t"+ r + ",-"+loadEntity.getOffset()+ "($s0)\n")
        
        elif loadEntity.getEntType() == "Variable" and entNestingL == nestingLevel:
            mipsfile.write("lw    $t"+r+", -"+loadEntity.getOffset()+"($sp)\n")  
        elif loadEntity.getEntType() == "Parameter" and entNestingL == nestingLevel and loadEntity.getParMode() == "in":
            mipsfile.write("lw    $t"+r+", -"+str(loadEntity.getOffset())+"($sp)\n")      
        
        elif loadEntity.getEntType() == "TempVariable":
            mipsfile.write("lw $t"+r+", -"+loadEntity.getOffset()+"($sp)\n" )
        
        elif loadEntity.getEntType() == "Parameter" and loadEntity.getParMode == "inout" and  entNestingL == nestingLevel:
            mipsfile.write("lw $t0,-"+loadEntity.getOffset()+"($sp)\n" )
            mipsfile.write("lw  $t"+r+", 0($t0)\n" )
        
        elif (loadEntity.getEntType() == "Variable" and entNestingL < nestingLevel):
            gnvlcode(v)
            mipsfile.write("lw  $t"+r+", 0($t0)\n")      
        
        elif (loadEntity.getEntType() == "Parameter" and loadEntity.getParMode() == "in" and entNestingL < nestingLevel):
            gnvlcode(v)
            mipsfile.write("lw    $t"+r+", 0($t0)\n")
       
        elif loadEntity.getEntType() == "Parameter" and loadEntity.getParMode() == "inout"  and entNestingL < nestingLevel:
            gnvlcode(v)
            mipsfile.write("lw    $t0, 0($t0)\n")
            mipsfile.write("lw    $t"+r+", 0($t0)\n")
        else:
            return
    
    
def storerv(r,v): #metafora dedomenwn apo ton kataxwriti r sthn mnhmh(to v)
    entstore = findEnt(v)
    if entstore == None:
       return
    nestingLevel = scopesList[-1].get_nestLevel() #trexon
    entNestingL = getEntNestingLevel(entstore.getName()) 
    
    if entstore.getEntType() == "Variable" and entNestingL == 0: #katholiki
        mipsfile.write("sw $t"+r +",-"+entstore.getOffset()+"($s0)\n")
    
    elif entstore.getEntType() == "Variable" and entNestingL == nestingLevel:
        mipsfile.write("sw $t"+r+", -"+entstore.getOffset()+"($sp)\n")
    elif entstore.getEntType() == "Parameter" and entstore.getParMode == "in" and entNestingL == nestingLevel:
        mipsfile.write("sw $t"+r+", -"+entstore.getOffset()+"($sp)\n")
    elif entstore.getEntType() == "TempVariable":
        mipsfile.write("sw $t"+r+", -"+entstore.getOffset()+"($sp)\n")
    
    elif entstore.getEntType() == "Parameter" and entNestingL == nestingLevel and entstore.getParMode() == "inout":
        mipsfile.write("lw $t0, -"+str(entstore.getOffset())+"($sp)\n")
        mipsfile.write("sw $t"+r+"0($t0)\n")
       
    elif entstore.getEntType() == "Variable" and entNestingL < nestingLevel:
        gnvlcode(v)
        mipsfile.write("sw $t"+r+",0($t0)\n")
    elif entstore.getEntType() == "Parameter" and entNestingL < nestingLevel and entstore.getParMode() == "in":
        gnvlcode(v)
        mipsfile.write("sw $t"+r+",0($t0)\n")
    
    elif entstore.getEntType() == "Parameter" and entstore.getParMode() == "inout" and entNestingL < nestingLevel:
        gnvlcode(v)
        mipsfile.write("lw $t0,0($t0)\n")
        mipsfile.write("sw $t"+r+",0($t0)\n")
 
def branch(x):
    if x == "=":
        return "beq"
    elif x == "<>":
        return "bne"
    elif x == ">":
        return "bgt"
    elif x == "<":
        return "blt"
    elif x == ">=":
        return "bge"
    elif x == "<=":
        return "ble"
        
def arithOper(x):
    if x == "+":
        return "add"
    elif x == "-":
        return "sub"
    elif x == "*":
        return "mul"
    elif x == "/":
        return "div"

def makeAssembly(asname):
    global mipsfile
    s = asname + ".asm"
    mipsfile = open(s ,"w+")
    for qu in quadsList:
        mips_code_file(qu, name)

def mips_code_file(qu, name):
    global actualList,mipsfile
    q=qu.split()
        
    if str(quadsList.index(qu)) == "0":
        mipsfile.write("j Lmain\n")
        insideMainFlag=True
        
    if name == progName: # gia main
        mipsfile.write("\n Lmain: \n")
    else:
        mipsfile.write("\n L_"+str(quadsList.index(qu))+":") # gia synartisis
        
    if q[0] == "jump":
        mipsfile.write("j L_"+q[3]+"\n")
            
    elif (q[0] in oper): #["=","<=",">=",">","<","<>"]
        loadvr(q[1], '1')
        loadvr(q[2], '2')
        mipsfile.write(branch(q[0]) + " $t1, $t2, L"+q[3]+"\n")
        
    elif q[0] == ":=":
        loadvr(q[1],'1')
        storerv('1',q[3])
            
    elif q[0] in symbols:#["+","-","/","*"]
        loadvr(q[1],'1')
        loadvr(q[2],'2')
        mipsfile.write(arithOper(q[0])+" $t1, $t1, $t2\n")
        storerv('1', q[3])
        
    elif q[0] == "out":
        mipsfile.write("li $v0,1\n")
        loadvr(q[1],",$a0")
        mipsfile.write("syscall\n")
            
    elif q[0] == "in":
        mipsfile.write("li $v0,5\n")
        mipsfile.write("syscall\n")
        storerv("$v0",q[1])
            
    elif q[0] == "retv":
        loadvr(q[1],'1')
        mipsfile.write("lw $t0,-8($sp)\n")
        mipsfile.write("sw $t1,0($t0)\n")

    elif q[0] == "par":
        if name != progName:
            if findEntByType(name,"Function") == None:
                return
            call,callNestLevel = findEntByType(name,"Function")
            framelength=call.getFramelength()
        else:
            callNestLevel = 0
            framelength = progFramelength
                
        if not actualList:
            mipsfile.write(" addi    $fp, $sp,"+ framelength +"\n")
            
            actualList.append(q)
            actIndex = actualList.index(q)
            par_offset = 12 + 4 * actIndex
            
            if q[2] == 'CV':
                loadvr(q[1], '0')
                mipsfile.write("sw $t0, -"+ par_offset+"($fp)\n")
            elif q[2] == 'REF':
                var= findEnt(q[1])
                varNestLevel = getEntNestingLevel(q[1])
                if callNestLevel == varNestLevel:
                    if var.getEntType() == "Variable" or (var.getEntType() == "Parameter" and var.getParMode() == "in"):
                        mipsfile.write("addi  $t0, $sp, -"+ var.getOffset()+"\n")
                        mipsfile.write("sw    $t0, -"+par_offset+"($fp)\n")
                    elif var.getEntType() == "Parameter" and var.getParMode() == "inout":
                        mipsfile.write("lw    $t0, -"+var.getOffset()+"($sp)\n")
                        mipsfile.write("sw    $t0, -"+par_offset+"($fp)\n")
                else:
                    if var.getEntType() == 'Variable' or (var.getEntType() == 'Parameter' and var.getParMode() == 'in'):
                        gnvlcode(q[1])
                        mipsfile.write("sw    $t0, -"+par_offset+"($fp)\n")
                    elif var.getEntType() == 'Parameter' and var.getParMode() == 'inout':
                        gnvlcode(q[1])
                        mipsfile.write("lw    $t0, 0($t0)\n")
                        mipsfile.write("sw    $t0, -"+par_offset+"($fp)\n")
            elif q[2] == 'RET':
                var = search_entity(q[1])
                varNestLevel = getEntNestingLevel(q[1])
                mipsfile.write("addi    $t0, $sp, -"+var.getOffset()+"\n")
                mipsfile.write("sw    $t0, -8($fp)\n")
            
    elif q[0] == "call":
        if name != progName:
            call = findEnt(name)
            if call==None:
                return
            callNestLevel = getEntNestingLevel(name)
            framelength=call.getFramelength()
        else:
            callNestLevel = 0
            framelength = progFramelength
        currentcall = findEnt(q[1])
        currentcallNestLevel = getEntNestingLevel(q[1])
            
        if actualList:
            el = actualList[-1]
            if el[2] == "RET":
                actualList.pop()
        else:
            mipsfile.write("addi    $fp, $sp,"+framelength+"\n")
            
        if callNestLevel == currentcallNestLevel:
            mipsfile.write("lw $t0, -4($sp)\n")
            mipsfile.write("sw $t0, -4($fp)\n")
        else:
            mipsfile.write(" sw    $sp, -4($fp)\n")
        mipsfile.write("addi $sp, $sp," +framelength+"\n")
        mipsfile.write("jal  L_"+to_call.getStartQ()+"\n")
        mipsfile.write("addi $sp, $sp,"+framelength+"\n")
            
        
    elif q[0] == "begin_block" :
        if name == progName:
            mipsfile.write("addi $sp, sp,"+str(progFramelength )+" \n")
            mipsfile.write("move $s0, $sp\n")
        if name != progName:
            mipsfile.write("sw $ra, -0($sp)\n")

    elif q[0] == "end_block" :
        if name == progName:
            mipsfile.write("j L_"+str(quadsList.index(qu))+"\n")
            mipsfile.write("jr $ra\n")
        else:
            mipsfile.write("lw $ra, 0($sp)\n")
            mipsfile.write("jr $ra\n")
                


######### MAIN ###############################
##############################################  

lex1()
program() 


    
    
    
    
    
    
    
    
    
    
    