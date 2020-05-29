#include "pch.h"
#include<iostream>
#include<vector>
#include<map>
#include<set>
#include<string>
#include<fstream>
#include<string.h>
using namespace std;

FILE	*f_sentence;			// 待分析语句文件
FILE	*f_grammer;				// 语法分析文法文件
ofstream f_Projset;
ofstream f_table;
ofstream f_process;
ofstream f_first;

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
vector<string>	sentence;		// 待分析语句
vector<vector<string>> grammer; // 文法产生式集合，char->string1, string2, string3...
set<string> Vn;					// 非终结符集合
set<string> Vt;					// 终结符集合
map<string, set<string>> first;	// first集合
vector<set<proj>> Proj_set;		// 项目集族
map<pair<int, string>, string> action;	// action表
map<pair<int, string>, string> go_to;	// goto表

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
		if(produce.size() > 0){
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
		if(temp.size() > 0)
			sentence.push_back(temp);

		if (ch == EOF)
			break;
		else
			continue;
	} while (1);
	sentence.push_back("$");	// 结束符号压栈
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
	if (action.find(make_pair(state, sentence[0])) == action.end())
	{
		if (action.find(make_pair(state, sentence[0])) == action.end())
		{
			// ("ERROR：没有与[%d,%s]对应的action或goto表项", state, sentence[0]);
			return -1;
		}
		else
		{
			nx_move = go_to[make_pair(state, sentence[0])];
		}
	}
	else
	{
		nx_move = action[make_pair(state, sentence[0])];
	}
	return 1;
}

void analyse()
{
	vector<string> sta;			// 分析栈
	sta.push_back("0");			// 初始状态
	int state;
	string nx_move;
	while (true)
	{
		if (toState(state, sta.back()) == -1)	// 解析当前状态
		{
			printf("ERROR：栈分析出错");
			break;
		}

		if (find_nx_move(state, nx_move) == -1)	// 解析下一步操作
		{
			printf("ERROR：没有与[%d,%s]对应的action或goto表项", state, sentence[0]);
			break;
		}

		if (nx_move[0] == 's')		//	SHIFT
		{
			sta.push_back(sentence.front());
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
			int i, pos = g.size() - 1;
			for (i = sta.size() - 1; i >= 0; i--)
			{
				if (isVn(sta[i]) || isVt(sta[i]))
				{
					if (sta[i] == g[pos])
						pos--;
				}
				if (pos == 0) break;
			}
			// 将i到sta.size()-1全部清空
			while (sta.size() != i)
			{
				sta.erase(sta.end() - 1);
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
}

int main()
{
	f_grammer = fopen("..\\..\\语法分析文法.txt", "r+");
	f_sentence = fopen("..\\..\\tokens.txt", "r+");
	f_Projset.open("..\\..\\lr_result\\生成项目集族.txt");
	f_table.open("..\\..\\lr_result\\生成action与goto表.txt");
	f_process.open("..\\..\\lr_result\\生成规约过程.txt");
	f_first.open("..\\..\\lr_result\\生成FIRST集合.txt");


	vector<string>front, back;
	set<string> A;
	back.push_back("S");
	A.insert("$");
	proj p("S'", front, back, A);
	set<proj> I;
	I.insert(p);	// 初始项目集[s'→·S, $]

	get_grammer_vn_vt();
	get_first();
	get_Projset(I);
	get_action_table();
	get_sentence();
	print();	// 打印first集合，action表、goto表、项目集族
	analyse();
}
