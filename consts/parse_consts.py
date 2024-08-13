fname = "arm_const.py"

lines = [line.rstrip('\n') for line in open(fname)]

for line in lines:
    if len(line) > 0 and line[0] == '#':
        continue
    tokens = line.split()
    if len(tokens) > 2:
        if tokens[2] == '0':
            #make a new list
            nameTok = tokens[0].split('_')
            listName = nameTok[1] +"_STRINGS"

            print "\n" + listName + " = {}"
        print "%s[%s] = \"%s\"" % (listName, tokens[2], tokens[0]) 
