#include "pch.h"
#include<iostream>
#include<vector>
#include<unordered_map>
#include<map>
#include<set>
#include<string>
#include<math.h>
#include<fstream>
#include<string.h>
using namespace std;

FILE	*f_sentence;			// 待分析语句文件
FILE	*f_grammer;				// 语法分析文法文件
ofstream f_Projset;
ofstream f_table;
ofstream f_process;
ofstream f_first;
ofstream f_code_inter;			// 中间代码
ofstream f_code;				// 目标代码

// 项目定义
struct proj							// 项目
{
	// [vn → front · back, ahead]
	string vn;
	vector<string> front;
	vector<string> back;
	set<string> ahead;
	proj(string vn, vector<string> front, vector<string> back, set<string> ahead) :
		vn(vn), front(front), back(back), ahead(ahead) {}

	void show()
	{
		cout << "[" << vn << "→";
		f_Projset << "[" << vn << "→";
		for (auto& s : front)
		{
			f_Projset << s;
			cout << s;
		}
		f_Projset << "·";
		cout << "·";
		for (auto& s : back)
		{
			f_Projset << s;
			cout << s;
		}
		f_Projset << ",";
		cout << ",";
		for (set<string>::iterator iter = ahead.begin(); iter != ahead.end(); iter++)
		{
			if (iter == ahead.begin())
			{
				f_Projset << *iter;
				cout << *iter;
			}
			else
			{
				f_Projset << "/" << *iter;
				cout << "/" << *iter;
			}
		}
		f_Projset << "]\n";
		cout << "]" << endl;
	}

	bool operator < (const proj& p1) const
	{
		if (vn < p1.vn)
		{
			return true;
		}
		else if (vn == p1.vn)
		{
			if (front.size() < p1.front.size())
				return true;
			else if (front.size() == p1.front.size())
			{
				for (int i = 0; i < front.size(); i++)
				{
					if (front[i] < p1.front[i])
						return true;
					else if (front[i] == p1.front[i])
						continue;
					else return false;
				}
				if (back.size() < p1.back.size())
					return true;
				else if (back.size() == p1.back.size())
				{
					for (int i = 0; i < back.size(); i++)
					{
						if (back[i] < p1.back[i])
							return true;
						else if (back[i] == p1.back[i])
							continue;
						else return false;
					}
					return ahead < p1.ahead;
				}
				else
					return false;
			}
			else
				return false;
		}
		else
			return false;
	}

};
vector<string> sema;			// 语义分析栈
vector<string> sta;				// 分析栈
vector<string>	sentence;		// 待分析语句
vector<vector<string>> grammer; // 文法产生式集合，char->string1, string2, string3...
set<string> Vn;					// 非终结符集合
set<string> Vt;					// 终结符集合
map<string, set<string>> first;	// first集合
vector<set<proj>> Proj_set;		// 项目集族
map<pair<int, string>, string> action;	// action表
map<pair<int, string>, string> go_to;	// goto表

struct v {
	string value;
	int reg;
	v() { reg = -1; }
};
unordered_map<string, v> symbol;		// new 符号表
vector<pair<int, vector<string> >> intercode;	// 中间代码<行号,内容>
vector<pair<int, vector<string> >> code;		// 中间代码<行号,内容>
vector<vector<int>> TFlist;				// 控制流语句和bool表达式 true list false list
int temp;								// 临时变量序号
int line;								// 代码行号
vector<set<string>> active;			    // 活跃信息
set<int> registers;						// 可用寄存器

bool isVt(string s)
{
	if (Vt.find(s) == Vt.end())
		return false;
	return true;
}

bool isVn(string s)
{
	if (Vn.find(s) == Vn.end())
		return false;
	return true;
}

void get_first()
{
	// 终结符的FIRST集合是本身
	for (auto& vt : Vt)
	{
		set<string> s;
		s.insert(vt);
		first[vt] = s;
	}
	// 终结符加入vn的first集合中
	for (auto& vn : Vn)
	{
		first[vn] = set<string>();
		for (auto& g : grammer)
			if (g[0] == vn && isVt(g[1]))
				first[vn].insert(g[1]);
	}
	// 加入vn的其他FIRST集合元素
	bool unfinish = true;
	while (unfinish)
	{
		unfinish = false;
		for (auto& vn : Vn)
		{
			for (auto& g : grammer)
			{
				// g[0] == vn 则该产生式左部为vn
				// isVn(g[1]) 则产生式右部的第一个符号是非终结符
				// g[1] != vn 该非终结符不是vn
				if (g[0] == vn && isVn(g[1]))
				{
					for (auto f : first[g[1]])
					{
						if (first[vn].find(f) == first[vn].end())
						{
							// 有first集合改变，则可能更新其他first集
							unfinish = true;
							first[vn].insert(f);
						}
					}
					// 产生式X→ABCDEF...
					// 如果$属于FIRST(A)且属于FIRST(B),则把C的FIRST集合加入到X的FIRST集合
					for (int i = 1; i < g.size(); i++) {
						if (isVn(g[i]))
						{
							if (first[g[i]].find("$") == first[g[i]].end()) {
								for (auto f : first[g[i]])
								{
									if (first[vn].find(f) == first[vn].end())
									{
										// 有first集合改变，则可能更新其他first集
										unfinish = true;
										first[vn].insert(f);
									}
								}
								break;
							}
						}
						else break;
					}
				}
			}
		}
	}
}

void closure(set<proj>& I) // 项目集的闭包
{
	int num, new_num;
	// 根据项目的back来求项目集的闭包
	// 直到没有更新为止
	bool unfinish = true;
	while (unfinish)
	{
		unfinish = false;
		for (auto& p : I)
		{
			// 假设项目p为[A→c·Bd, a]
			for (auto& g : grammer)
			{
				// 产生式的左部必须为B
				// 设产生式为B→e
				// 将[B→·e, FIRST(da)]加入到项目集
				if (p.back.size() > 0 && p.back[0] == g[0])
				{
					string vn = g[0];
					vector<string> front;	// front 总是空的
					vector<string> back = g;// back 是文法产生式的右部
					back.erase(back.begin());
					// 求上述的FIRST(da)
					set<string> ahead;
					if (p.back.size() == 1)
					{
						// p.back只有B
						// 则将p的ahead集合的全部FIRST加入
						for (auto& a : p.ahead)
							for (auto& pa : first[a])
								if (ahead.find(pa) == ahead.end())
									ahead.insert(pa);
					}
					else
					{
						// p.back不止有B
						//if (p.ahead.size() == 1 && p.ahead.find("$") != p.ahead.end())
						//{
							// p.ahead只有$时，则把p.back第二个符号的first集合加入
						for (auto& a : first[p.back[1]])
						{
							if (ahead.find(a) == ahead.end())
								ahead.insert(a);
						}
						//}
						/*
						else
						{
							// p.ahead不只有$
							for (auto& a : p.ahead)
								for (auto& pa : first[a])
									if (ahead.find(pa) == ahead.end())
										ahead.insert(pa);
						}*/
					}
					proj pro(vn, front, back, ahead);
					if (I.find(pro) == I.end()) {
						unfinish = true;
						I.insert(pro);
					}
				}
			}
		}
	}
}

void get_grammer_vn_vt()		// 读取文法到grammer中
{
	char ch;
	// 表示每一行一个产生式
	vector<string> produce;
	// 终结符应包含结束符
	Vt.insert("$");
	do
	{
		string temp;
		ch = fgetc(f_grammer);
		temp += ch;
		while (ch != EOF && ch != '\n')
		{
			ch = fgetc(f_grammer);
			if (ch == ' ' || ch == EOF || ch == '\n')
			{
				// 非终结符首字母总不是大写字母
				if (temp[0] < 'A' || temp[0] >= 'Z')
				{
					Vt.insert(temp);
				}
				produce.push_back(temp);
				temp.clear();
				if (ch == EOF || ch == '\n')
				{
					break;
				}
			}
			else
			{
				temp += ch;
			}
		}
		if (produce.size() > 0) {
			grammer.push_back(produce);
			Vn.insert(produce[0]);
			produce.clear();
		}
	} while (ch != EOF);
}

bool inProj_set(const set<proj>& newp)
{
	for (int i = 0; i < Proj_set.size(); i++)
	{
		if (newp.size() != Proj_set[i].size())
			continue;
		bool equal = true;
		for (auto& p : newp)
		{
			if (Proj_set[i].find(p) == Proj_set[i].end())
			{
				equal = false;
				break;
			}
		}
		if (equal) return true;
	}
	return false;
}

int index_Proj_set(const set<proj>& newp)
{
	for (int i = 0; i < Proj_set.size(); i++)
	{
		if (newp.size() != Proj_set[i].size())
			continue;
		bool equal = true;
		for (auto& p : newp)
		{
			if (Proj_set[i].find(p) == Proj_set[i].end())
			{
				equal = false;
				break;
			}
		}
		if (equal) return i;
	}
	return Proj_set.size();
}

set<proj> go(const set<proj>& I, string next)
{
	set<proj> newPro;
	// next = B; [A→c·Bd, a] -> [A→cB·d, a]
	for (auto& p : I)
	{
		if (p.back.size() > 0 && p.back[0] == next)
		{
			vector<string>front, back;
			front = p.front;
			front.push_back(next);
			back = p.back;
			back.erase(back.begin());
			proj pro(p.vn, front, back, p.ahead);
			if (newPro.find(pro) == newPro.end())
			{
				newPro.insert(pro);
				closure(newPro);
			}
		}
	}
	return newPro;
}

void get_Projset(set<proj>& I)						// 计算项目集族
{
	closure(I);
	Proj_set.push_back(I);
	// 构造Proj_set的同时，建立action部分表和goto表
	for (int i = 0; i < Proj_set.size(); i++) {
		for (auto& vn : Vn)
		{
			set<proj> newPro = go(Proj_set[i], vn);
			if (newPro.size() > 0 && !inProj_set(newPro))
			{
				go_to[make_pair(i, vn)] = to_string(Proj_set.size());			// i加入goto
				Proj_set.push_back(newPro);
			}
			else if (inProj_set(newPro))
			{
				go_to[make_pair(i, vn)] = to_string(index_Proj_set(newPro));	// i加入goto
			}
		}
		for (auto& vt : Vt)
		{
			set<proj> newPro = go(Proj_set[i], vt);
			if (newPro.size() > 0 && !inProj_set(newPro))
			{
				action[make_pair(i, vt)] = "s" + to_string(Proj_set.size());		// sj加入action
				Proj_set.push_back(newPro);
			}
			else if (inProj_set(newPro))
			{
				action[make_pair(i, vt)] = "s" + to_string(index_Proj_set(newPro));	// sj加入action
			}
		}
	}
}

void get_action_table()						// 计算action表余项acc与rj
{
	vector<string>front, back;
	front.push_back("S");
	set<string> A;
	A.insert("$");
	proj p("S'", front, back, A);
	for (int i = 0; i < Proj_set.size(); i++)
	{
		if (Proj_set[i].find(p) != Proj_set[i].end())
		{
			action[make_pair(i, "$")] = "acc";	// acc加入action
		}
	}
	// 建立剩余rj的项
	for (int i = 0; i < Proj_set.size(); i++)
	{
		for (auto& p : Proj_set[i])
		{
			if (p.back.size() != 0 || p.vn == "S'")
				continue;

			for (int j = 0; j < grammer.size(); j++)
			{
				if (grammer[j][0] == p.vn && grammer[j].size() - 1 == p.front.size())
				{
					for (int k = 1; k < grammer[j].size(); k++)
					{
						if (grammer[j][k] == p.front[k - 1])
						{
							if (k == grammer[j].size() - 1)
							{
								// 产生式和项目vn+front完全相同
								for (auto s : p.ahead)
									action[make_pair(i, s)] = "r" + to_string(j);	// rj加入到action
							}
						}
						else
							break;
					}
				}
			}

		}
	}
}

void get_sentence()						// 获取待分析句子
{
	char ch;
	string temp;
	do
	{
		string temp;
		ch = '_';

		while (ch != '\t' && ch != EOF)	// 待分析语句文件每个符号用tap隔开
		{
			ch = fgetc(f_sentence);
			if (ch != '\t' && ch != EOF)
				temp += ch;
		}
		// 这里改一下，遇id把id后的字符串加到符号表
		// 遇val将数字转化为其后缀
		if (temp.size() > 0)
		{
			sentence.push_back(temp);
			if (temp == "id" || temp == "val")// || temp == "f")
			{
				string temp_nx;
				ch = '_';
				// while循环为找到id或val之后的一个字符串
				while (ch != '\t' && ch != EOF)	// 待分析语句文件每个符号用tap隔开
				{
					ch = fgetc(f_sentence);
					if (ch != '\t' && ch != EOF)
						temp_nx += ch;
				}
				// 把id或val加到符号表
				// val的数字变成其后缀，规约时候用
				if (temp == "id" && symbol.find(temp_nx) == symbol.end())
				{
					v p;
					symbol[temp_nx] = p;
				}

				sentence.pop_back();
				sentence.push_back(temp + temp_nx);
			}
		}
		// {  while || && 后边增加m，但main后不加
		if (temp == "{" || temp == "while" || temp == "||" || temp == "&&")
		{ 
			if(sentence[sentence.size()-4] != "f")
				sentence.push_back("m");
		}
		else if (temp == "else") 
		{
			sentence[sentence.size() - 1] = "n";
			sentence.push_back("else");
		}
		
		if (ch == EOF)
			break;
		else
			continue;
	} while (1);
	sentence.push_back("$");	// 结束符号压栈
	for (auto s : sentence)
		cout << s << endl;
}

int toState(int& state, string s)		// 状态栈中的字符串转为数字，以索引action和go表
{
	if (s[0] == '0' && s.length() > 1)
		return -1;
	for (int i = 0; i < s.length(); i++)
	{
		if (s[i] < '0' || s[i] > '9')
			return -1;
	}
	int res = 0;
	for (char c : s)
	{
		res = res * 10 + (c - '0');
	}
	if (res >= Proj_set.size())
		return -1;
	state = res;
	return state;
}

int find_nx_move(int state, string& nx_move)
{
	string temp = sentence[0];
	if (temp.substr(0, 2) == "va")
	{
		temp = "val";
	}
	else if (temp.substr(0, 2) == "id")
	{
		temp = "id";
	}
	else if (temp.substr(0, 1) == "f" && temp != "float")
	{
		temp = "f";
	}
	if (action.find(make_pair(state, temp)) == action.end())
	{
		if (action.find(make_pair(state, temp)) == action.end())
		{
			// ("ERROR：没有与[%d,%s]对应的action或goto表项", state, sentence[0]);
			return -1;
		}
		else
		{
			nx_move = go_to[make_pair(state, temp)];
		}
	}
	else
	{
		nx_move = action[make_pair(state, temp)];
	}
	return 1;
}

string newtemp()
{
	return "t" + to_string(temp++);
}

void backpatch(const vector<int>& list, int quad)
{
	for (auto i : list)
	{
		for (auto& info : intercode)
		{
			if (info.first == i)
			{
				info.second.push_back(to_string(quad));
			}
		}
	}
}

void merge(vector<vector<int>> & list, int a, int b)
{
	// 将倒数第b个vector合并到倒数第a个，并将倒数第b个删除
	for (auto i : list[list.size() - b])
		list[list.size() - a].push_back(i);
}

void genInterCode(int reduce_g, const vector<string>& g)
{
	pair<int, vector<string>> emit;
	vector<string> code;
	int len = sema.size();
	if (reduce_g == 28 || reduce_g == 29)
	{
		//D -> id = E;
		//D -> id = E, D
		code = { sema[len - 2] , "=", sema[len - 1] };
		emit = make_pair(line++, code);
		intercode.push_back(emit);
		sema.pop_back();
		sema.pop_back();
	}
	else if (reduce_g == 30 || reduce_g == 31 || reduce_g == 33 || reduce_g == 34)
	{
		string op =  reduce_g == 30 ? "+" :
						reduce_g == 31 ? "-" :
						reduce_g == 32 ? "/" :
						"*";
		//E -> E + T
		//E -> E - T
		string t = newtemp();
		// tnew = E relop T
		code = { t, "=", sema[len - 2], op, sema[len - 1] };
		emit = make_pair(line++, code);
		intercode.push_back(emit);
		symbol[t] = v();
		sema.pop_back();
		sema.pop_back();
		sema.push_back(t);
	}
	else if (reduce_g == 45 || reduce_g == 46 || reduce_g == 47 || reduce_g == 48)
	{
		//M -> E == E
		//M -> E < E
		//M -> E > E
		//M -> E != E
		// TFlist:  ...... E.truelist E.falselist 
		TFlist.push_back(vector<int>(1, line));
		TFlist.push_back(vector<int>(1, line + 1));
		// 存储两条语句，序号分别为line 和 line+1
		string relop = reduce_g == 45 ? "==" :
			reduce_g == 46 ? "<" :
			reduce_g == 47 ? ">" :
			"!=";
		code = { "if ", sema[len - 2], relop, sema[len - 1], " goto " };
		emit = make_pair(line++, code);
		intercode.push_back(emit);
		code = { "goto " };
		emit = make_pair(line++, code);
		intercode.push_back(emit);
		// 附加栈sta出栈
		sema.pop_back();
		sema.pop_back();
	}
	else if (reduce_g == 41)
	{
		//C -> M && K M
		// 回填
		vector<int> & E1_truelist = TFlist[TFlist.size() - 5];
		int Mquad = TFlist[TFlist.size() - 3][0];
		backpatch(E1_truelist, Mquad);
		// 合并链表
		// 将M.quad出栈
		TFlist.erase(TFlist.end() - 3);
		// 现在TFlist结构: .....E1.truelist E1.falselist E2.truelist E2.falselist
		// 合并E1.falselist E2.falselist
		merge(TFlist, 3, 1);
		TFlist[TFlist.size() - 4] = TFlist[TFlist.size() - 2];
		// E2.truelist E2.falselist出栈
		TFlist.pop_back();
		TFlist.pop_back();
	}
	else if (reduce_g == 42)
	{
		//C -> M || K M
		// 回填
		vector<int> & E1_falselist = TFlist[TFlist.size() - 4];
		int Mquad = TFlist[TFlist.size() - 3][0];
		backpatch(E1_falselist, Mquad);
		// 合并链表
		// 将M.quad出栈
		TFlist.erase(TFlist.end() - 3);
		// 现在TFlist结构: .....E1.truelist E1.falselist E2.truelist E2.falselist
		// 合并E1.truelist E2.truelist
		merge(TFlist, 4, 2);
		TFlist[TFlist.size() - 3] = TFlist[TFlist.size() - 1];
		// E2.truelist E2.falselist出栈
		TFlist.pop_back();
		TFlist.pop_back();
	}
	else if (reduce_g == 43)
	{
		// M -> ! M
		// E.truelist = E.falselist  E.falselist = E.truelist
		vector<int> temp = TFlist.back();
		TFlist[TFlist.size() - 1] = TFlist[TFlist.size() - 2];
		TFlist[TFlist.size() - 2] = temp;
	}
	else if (reduce_g == 14)
	{
		// W -> while K ( C ) { K B }
		// 现在TFlist结构: .....M1 E.truelist E.falselist M2
		vector<int> E_truelist = TFlist[TFlist.size() - 3];
		vector<int> E_falselist = TFlist[TFlist.size() - 2];
		int M2quad = TFlist[TFlist.size() - 1][0];
		int M1quad = TFlist[TFlist.size() - 4][0];
		// 回填
		backpatch(E_truelist, M2quad);

		code = { "goto " , to_string(M1quad) };
		emit = make_pair(line++, code);
		intercode.push_back(emit);
		// 留下一个S链表
		vector<int> S = E_falselist;
		// TFlist出栈4个
		int pop_ = 4;
		while (pop_ -- > 0) 
			TFlist.pop_back();

		// 这里把while条件错误时的跳转解决了
		backpatch(S, line);
	}
	else if (reduce_g == 15)
	{
		// I -> if ( C ) { K B }
		int len = TFlist.size();
		backpatch(TFlist[len - 3], TFlist[len - 1][0]);
		// S
		vector<int> S = TFlist[len - 2];

		int pop_ = 3;
		while (pop_-- > 0)
			TFlist.pop_back();

		backpatch(S, line);
	}
	else if (reduce_g == 16)
	{
		// I -> if ( C ) { K B } Q else { K B }
		// 现在TFlist结构: .....E.truelist E.falselist M1 N M2
		int len = TFlist.size();
		backpatch(TFlist[len - 5], TFlist[len - 3][0]);
		backpatch(TFlist[len - 4], TFlist[len - 1][0]);
		// S
		vector<int> S = TFlist[len - 2];

		int pop_ = 5;
		while (pop_-- > 0)
			TFlist.pop_back();

		backpatch(S, line);
	}
	else if (reduce_g == 49)
	{
		// K -> m
		TFlist.push_back(vector<int>(1, line));
	}
	else if (reduce_g == 50)
	{
		// Q -> n
		// N else 的行号加入栈中
		TFlist.push_back(vector<int>(1, line));

		code = { "goto " };
		emit = make_pair(line++, code);
		intercode.push_back(emit);
	}
}

void analyse()
{
	temp = 0;			// 中间临时变量序号
	line = 100;			// 中间代码顺序


	sta.push_back("0");			// 初始状态

	int state;
	string nx_move;
	while (true)
	{
		if (toState(state, sta.back()) == -1)	// 解析当前状态
		{
			cout << "状态解析错误" << endl;
			exit(0);
			break;
		}

		if (find_nx_move(state, nx_move) == -1)	// 解析下一步操作
		{
			cout << "ERROR：没有与[" << state << "," << sentence[0] << "]对应的action或goto表项" << endl;
			exit(0);
		}

		if (nx_move[0] == 's')		//	SHIFT
		{
			// id 或 val
			string temp = sentence.front();
			if (sentence.front().substr(0, 2) == "va")
			{
				sema.push_back(temp.substr(3, temp.length() - 3));
				sta.push_back("val");
			}
			else if (sentence.front().substr(0, 2) == "id")
			{
				sema.push_back(temp.substr(2, temp.length() - 2));
				sta.push_back("id");
			}
			/*else if (sentence.front().substr(0, 1) == "f" && temp != "float")
			{
				//sema.push_back(temp.substr(1, temp.length() - 1));
				sta.push_back("f");
			}*/
			else
			{
				sta.push_back(sentence.front());
			}
			sta.push_back(nx_move.substr(1, nx_move.length()));
			sentence.erase(sentence.begin());
		}
		else if (nx_move[0] == 'r')	// REDUCE
		{
			int reduce_g = toState(reduce_g, nx_move.substr(1, nx_move.length()));
			vector<string> g = grammer[reduce_g];

			/*这里规约产生式*/
			for (auto s : g)
			{
				f_process << s << '\t';
			}
			f_process << "\n";

			// 生成中间代码
			genInterCode(reduce_g, g);

			int i, pos = g.size() - 1;
			for (i = sta.size() - 1; i >= 0; i--)
			{
				if (isVn(sta[i]) || isVt(sta[i]))
				{
					if (sta[i] == g[pos])
					{
						pos--;
					}
				}
				if (pos == 0) break;
			}
			// 将i到sta.size()-1全部清空
			while (sta.size() != i)
			{
				sta.pop_back();
			}

			// 压入规约产生式左部
			toState(state, sta.back());
			sta.push_back(g[0]);

			sta.push_back(go_to[make_pair(state, g[0])]);
		}
		else if (nx_move == "acc")	// ACCEPT
		{
			printf("accept\n");
			break;
		}
		else
		{
			printf("ERROR：待分析语句有非终结符%s", sentence.front());
			break;
		}
	}
}

void print()
{
	f_first << "FIRST集：\n";
	for (auto& f : first) {
		cout << f.first << ":    ";
		f_first << f.first << ":   ";
		for (auto& t : f.second)
		{
			f_first << " " << t;
			cout << " " << t;
		}
		cout << endl;
		f_first << "\n";
	}

	int i = 0;
	for (auto& I : Proj_set)
	{
		cout << "第" << i << "个项目集" << endl;
		f_Projset << "第" << i << "个项目集\n";
		i++;
		for (auto p : I)
			p.show();
		f_Projset << "\n";
	}
	get_action_table();

	f_table << "action表：" << action.size() << "项\n";
	cout << "\naction表：" << action.size() << "项\n";
	for (auto& m : action)
	{
		f_table << m.first.first << "\t" << m.first.second << "\t" << m.second << "\n";
		cout << m.first.first << "\t" << m.first.second << "\t" << m.second << endl;
	}

	f_table << "\ngoto表：" << go_to.size() << "项\n";
	cout << "\ngoto表：" << go_to.size() << "项\n";
	for (auto& m : go_to)
	{
		f_table << m.first.first << "\t" << m.first.second << "\t" << m.second << "\n";
		cout << m.first.first << "\t" << m.first.second << "\t" << m.second << endl;
	}

	f_code_inter << "中间代码\n";
	for (auto line : intercode)
	{
		f_code_inter << to_string(line.first) << "  ";
		for (auto l : line.second)
			f_code_inter << l;
		f_code_inter << "\n";
	}

	for (auto line : code)
	{
		f_code << to_string(line.first) << "  ";
		for (auto l : line.second)
			f_code << l << "  ";
		f_code << "\n";
	}
}

void getActive()
{
	vector<set<string>> symbols;
	symbols.resize(intercode.size());
	for (int i = 0; i < intercode.size(); i++)
	{
		for (auto temp : intercode[i].second)
		{
			if (symbol.find(temp) != symbol.end())
			{
				symbols[i].insert(temp);
			}
		}
	}

	// active[i]中存储第i行代码中的在之后会活跃的标识符
	active.resize(intercode.size());
	for (int i = 0; i < intercode.size(); i++)
	{
		if (symbols[i].size() == 0)
			continue;
		for(auto temp : symbols[i])
		{
			for (int j = i + 1; j < intercode.size(); j++)
			{
				if (symbols[j].size() == 0)
					continue;
				if (symbols[j].find(temp) != symbols[j].end())
				{
					active[i].insert(temp);
					break;
				}
			}
		}
	}
}

int getreg(string id, int line)
{
	if (symbol[id].reg == -1)
	{
		if (registers.size() > 0) 
		{
			int res = *registers.begin();
			symbol[id].reg = res;
			registers.erase(registers.begin());
			return res;
		}
		cout << "无寄存器可用！" << endl;
	}
	// 如果id是第line行的第一个符号，并且第二个符号不活跃了
	if (id == intercode[line].second[0])
	{
		string id2 = intercode[line].second[2];
		if (active[line].find(id2) == active[line].end() && 
			symbol.find(id2)!=symbol.end() && symbol[id2].reg != -1)
		{
			registers.insert(symbol[id].reg);
			symbol[id].reg = symbol[id2].reg;
			symbol[id2].reg = -1;
			return symbol[id].reg;
		}
	}
	return symbol[id].reg;
}

void getCode()
{
	for (int i = 1; i <= 18; i++)
		registers.insert(i);

	for (int i = 0; i < intercode.size(); i++)
	{
		// 代码分四种情况：a = b | a = b + c | if a<b goto line | goto line
		// a = b			 ：	addi $a $b 0
		// a = b + c		 ：	addi $a $b $c
		// if a < b goto line：	beq bne bgt blt $a $b offset
		// goto line		 ：	J offset
		int len = intercode[i].second.size();
		vector<string> & line = intercode[i].second;
		vector<string>	tmpc;
		if (len == 3)
		{
			// a = b
			if (symbol.find(line[2]) != symbol.end())// b 为标识符
			{
				int regb = getreg(line[2], i);
				int rega = getreg(line[0], i);
				tmpc = {"addi","$"+to_string(rega), "$" + to_string(regb), "0"};
				code.push_back({ intercode[i].first, tmpc });
			}
			else // b 为常数
			{
				int rega = getreg(line[0], i);
				tmpc = { "addi","$" + to_string(rega), "$0", line[2]};
				code.push_back({ intercode[i].first, tmpc });
			}
		}
		else if (len == 5)
		{
			// a = b + c
			int regb = -1, regc = -1;
			if (symbol.find(line[2]) != symbol.end())
				regb = getreg(line[2], i);
			if (symbol.find(line[4]) != symbol.end())
				regc = getreg(line[4], i);

			int rega = getreg(line[0], i);

			string op = line[3] == "+" ? "add" : line[3] == "-" ? "sub" :
				line[3] == "*" ? "mul" : "div";
			tmpc = {op, "$"+to_string(rega)};
			tmpc.push_back(regb == -1 ? line[2] : "$" + to_string(regb));
			tmpc.push_back(regc == -1 ? line[4] : "$" + to_string(regc));
			code.push_back({ intercode[i].first, tmpc });
		}
		else if (len == 6)
		{
			// if a < b goto line
			int rega = -1, regb = -1;
			if (symbol.find(line[1]) != symbol.end())
				rega = getreg(line[1], i);
			if (symbol.find(line[3]) != symbol.end())
				regb = getreg(line[3], i);

			string op = line[2] == ">" ? "bgt" : line[2] == "<" ? "blt" :
				line[2] == "==" ? "beq" : "bnq";
			tmpc.push_back(op);
			tmpc.push_back(rega == -1 ? line[1] : "$" + to_string(rega));
			tmpc.push_back(regb == -1 ? line[3] : "$" + to_string(regb));
			// offset
			tmpc.push_back(to_string(atoi(line[5].c_str()) - intercode[i].first));
			code.push_back({ intercode[i].first, tmpc });
		}
		else if (len == 2)
		{
			// goto line
			tmpc = { "j", line[1] };
			code.push_back({ intercode[i].first, tmpc });
		}
	}
}

int main()
{
	f_grammer = fopen("..\\..\\语法分析文法.txt", "r+");
	f_sentence = fopen("..\\..\\tokens.txt", "r+");
	f_Projset.open("..\\..\\lr_result\\生成项目集族.txt");
	f_table.open("..\\..\\lr_result\\生成action与goto表.txt");
	f_process.open("..\\..\\lr_result\\生成规约过程.txt");
	f_first.open("..\\..\\lr_result\\生成FIRST集合.txt");
	f_code_inter.open("..\\..\\中间代码.txt");
	f_code.open("..\\..\\目标代码.txt");

	vector<string>front, back;
	set<string> A;
	back.push_back("S");
	A.insert("$");
	proj p("S'", front, back, A);
	set<proj> I;
	I.insert(p);	// 初始项目集[s'→·S, $]

	get_grammer_vn_vt();

	// 36: F->val 35: F->id 37: F->f() 27~32:E->E+T~T->F 32: T->F 27:E->E+T
	// 15: A->int  17: A->float

	get_first();
	get_Projset(I);
	get_action_table();
	get_sentence();
	analyse();
	printf("符号表：\n");
	for (auto&s : symbol)
		cout << s.first << " ";
	cout << endl;

	getActive();
	getCode();

	print();	// 打印first集合，action表、goto表、项目集族、输入文件
}