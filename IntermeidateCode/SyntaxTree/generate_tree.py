dirs = "..\\lr_result\\生成规约过程.txt"
output = "tree_node_leaf.txt"
def generate():
    f = open(dirs)
    lines = f.readlines()
    # 翻转
    lines.reverse()
    para = []
    for line in lines:
        l1 = line.strip('\n')
        l2 = l1.strip('\t')
        l = l2.split('\t')
        para.append(l)
    f.close()
    # 返回规约产生式的倒序
    return para

if __name__ == "__main__":
    lines = generate()  #  读入节点
    context = ["digraph d {\n"]
    father = []
    nodecnt = 1
    s = '\tnode{} [label="{}"]\n'.format(nodecnt, lines[0][0])
    nodecnt = nodecnt + 1
    context.append(s)

    for i in range(1, len(lines[0])):
        father.append([nodecnt, lines[0][i]])
        s = '\tnode{} [label="{}"]\n'.format(nodecnt, lines[0][i])
        context.append(s)
        s = '\tnode{} -> node{}\n'.format(1, nodecnt)
        context.append(s)
        nodecnt = nodecnt + 1
    for i in range(1,len(lines)):
        curr_father_num = 0
        for j in range(len(lines[i])):
            if j == 0:
                k = len(father) - 1
                while(father[k][1] != lines[i][0]):
                    k = k - 1
                curr_father_num = father[k][0]
                father.remove(father[k])
            else:
                s = '\tnode{} [label="{}"]\n'.format(nodecnt, lines[i][j])
                context.append(s)
                s = '\tnode{} -> node{}\n'.format(curr_father_num, nodecnt)
                context.append(s)
                father.append([nodecnt, lines[i][j]])
                nodecnt = nodecnt + 1

    context.append("}")
    for i in context:
        print(i)    
    
    f = open(output,"w")
    for i in context:
        f.write(i)
    f.close()  


#dot -Tpng tree.dot -o s.png生成图片