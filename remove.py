import sys

if __name__ == '__main__':
    fi = open(sys.argv[1], 'r')
    flag = False
    for i in fi:
        if flag:
            if len(i) >= 11 and i[:11] == 'Assumptions':
                exit()
            print i,
        if len(i) >= 9 and i[:9] == 'Minimized':
            flag = True

    if flag: exit()

    fi = open(sys.argv[1], 'r')
    for i in fi:
        if flag:
            if len(i) >= 11 and i[:11] == 'Assumptions':
                exit()
            print i,
        if len(i) >= 9 and i[:9] == 'Inductive':
            flag = True
