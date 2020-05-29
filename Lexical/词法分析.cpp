#include "pch.h"
#include<iostream>
#include<vector>
#include<unordered_set>
#include<unordered_map>
#include<string>
#include<fstream>
#include<string.h>
using namespace std;

struct analyse {
	int line;
	int char_Num;
	int id_Num;
	int Deli_Num;
	int Mono_Num;
	int Bino_Num;
	int Key_Num;
	int IDF_Num;
	int Func_Num;
	analyse() {
		line = 0;
		char_Num = 0;
		id_Num = 0;
		Mono_Num = 0;
		Deli_Num = 0;
		Key_Num = 0;
		Bino_Num = 0;
		IDF_Num = 0;
		Func_Num = 0;
	}
	void show() {
		printf("行数\t字符数\t标识符\t分隔符\t单目运算符\t双目运算符\t关键字\t数字\t函数\n");
		printf("%d\t%d\t%d\t%d\t%d\t\t%d\t\t%d\t%d\t%d\n",
			line, char_Num, id_Num, Deli_Num, Mono_Num, Bino_Num, Key_Num, IDF_Num, Func_Num);
	}
};

ofstream output;
ofstream table;
FILE *C_source = NULL;
analyse Analy;

// 关键词
unordered_set<string> keyWords = 
{ 
	"char","continue","double","if","void",
	"else","float","include","bool","int",
	"return","while","stdio.h" 
};
// 单目运算符
unordered_set<char> Mono_Operator 
= { '+','-','*','/','!','~','&','|','^','=', '[', ']','<','>' , '#' ,'\''};
// 双目运算符
unordered_set<string> Bino_Operator 
= { "++","--","&&","||","<=","!=","==",">=","+=","-=","*=","/=" };
// 分隔符
unordered_set<char> Delimiter 
= { ',','(',')','{','}',';' };

unordered_map<string, string> key_output = 
{
		{"elseif","CIRCULATION"},{"if","BRANCH"},{"else","BRANCH"},{"while","CIRCULATION"}
};

static inline bool isInteger(char c)
{
	return c >= '0'&&c <= '9';
}

static inline bool isLetter(char c)
{
	return (c >= 'a'&&c <= 'z') || (c >= 'A'&&c <= 'Z');
}

static inline bool isDelimiter(char  c)
{
	return Delimiter.find(c) != Delimiter.end();
}

static inline bool isMono(char c)
{
	return Mono_Operator.find(c) != Mono_Operator.end();
}

static inline bool isBino(string s)
{
	return Bino_Operator.find(s) != Bino_Operator.end();
}

static inline bool isKey(string s)
{
	return keyWords.find(s) != keyWords.end();
}

static inline bool notRecog(char c)
{
	if (c == '?' || c == '@' || c == '、' || c == 127 || c == '$')
		return true;
	return false;
}

int INT(string s) {
	if (s.length() == 0)
		return -1;
	if (s.length() > 10)
		return false;
	return 1;
}

void scan_source()
{
	string str(100, '0');
	int pos;
	char ch;
	int flag;
	string func;

	bool finish = false;
	ch = fgetc(C_source);

	while (!finish)
	{
		pos = 0;
		flag = -1;
		if (isInteger(ch) || ch == '-') // 处理正负数字常量
		{
			flag = 1;
			str[pos++] = ch;
			ch = fgetc(C_source);
			//if(isInteger(ch))
			//{
			while (isInteger(ch))
			{
				str[pos++] = ch;
				ch = fgetc(C_source);
			}
			if (ch != ',' && ch != ';' && ch != ' ' && ch != '\t' && ch != '\t')
			{
				cout << "ERROR, NOT AN INTEGER!!! lines:" << Analy.line + 1<< endl;	// 错误
					exit(0);
			}
			else
			{
				// 数字常量的各种可能列举
				int num_typ = INT(str.substr(0, pos));
				Analy.IDF_Num++;
				if (num_typ == 1) {
					output << "val\t";
					cout << str.substr(0, pos) << "\t\t" << "int" << endl; // 整
				}
				else
				{
					cout << "ERROR, NOT AN INTEGER!!! lines:" << Analy.line + 1<< endl;	// 错误
					exit(0);
				}
				pos = 0;
			}
			//}
			//else
			//{
			//	flag = 3;
			//}
		}

		// 加载关键词或标识符
		if (isLetter(ch) && flag != 1)	
		{
			flag = 2;
			str[pos++] = ch;
			ch = fgetc(C_source);
			while (isLetter(ch) || isInteger(ch) 
				|| ch == '_' || ch == '.')
			{
				str[pos++] = ch;
				ch = fgetc(C_source);
			}
			if (notRecog(ch))
			{
				cout << "ERROR, NOT AN IDENTIFER!!! lines:" << Analy.line + 1 << endl;	// 错误
				exit(0);
			}
		}
		else if (isLetter(ch) && flag == 1)
		{
			cout << "ERROR, NOT AN INTEGER!!! lines:" << Analy.line + 1<< endl;	// 错误
			exit(0);
		}

		if (flag == 2)		// 处理关键词或标识符
		{
			if (isKey(str.substr(0, pos)))
			{
				if (key_output.find(str.substr(0, pos)) != key_output.end()) {
					output << str.substr(0, pos)+"\t";
					cout << str.substr(0, pos) << "\t\t" << key_output[str.substr(0, pos)] << endl;
				}
				else {
					output << str.substr(0, pos) + "\t";
					cout << str.substr(0, pos) << "\t\t" << "关键字" << endl;
				}
				Analy.Key_Num++;
			}
			else
			{
				// 标识符，或者函数名
				if (ch == '(')
				{
					
					str[pos++] = ch;
					// 找到函数结尾
					while (ch != ')') 
					{
						if (ch == EOF)
						{
							cout << "ERROR, NOT AN identifer!!! lines:" << Analy.line + 1<< endl;	// 错误
							exit(0);
						}
						ch = fgetc(C_source);
						str[pos++] = ch;
					}
					Analy.Func_Num++;
					output << "f\t(\t)\t";
					cout << str.substr(0, pos) << "\t\t" << "函数" << endl;
					ch = fgetc(C_source);
				}
				// 数组
				else if (ch == '[') {
					int start = pos;
					str[pos++] = ch;
					// 找到数组结尾
					ch = fgetc(C_source);
					while (ch != ']') 
					{
						if ( !isInteger(ch))
						{
							cout << "ERROR, NOT AN Array!!! lines:" << Analy.line + 1<< endl;	// 错误
							exit(0);
						}
						if (ch == EOF )
						{
							cout << "ERROR, NOT AN identifer!!! lines:" << Analy.line + 1<< endl;	// 错误
							exit(0);
						}
						
						str[pos++] = ch;
						ch = fgetc(C_source);
					}
					str[pos++] = ch;
					if (pos - start > 2) {
						output << "id";
						output << "\t";
						cout << str.substr(0, pos) << "\t\t" << "整型" << endl;
						Analy.IDF_Num++;
					}
					else {
						output << "a";
						output << "\t";
						cout << str.substr(0, pos) << "\t\t" << "数组" << endl;
					}
					ch = fgetc(C_source);
				}
				else
				{
					output << "id\t";

					cout << str.substr(0, pos) << "\t\t" << "标识符" << endl;
					Analy.id_Num++;
				}
			}
			Analy.char_Num += pos;
			pos = 0;
		}

		if (isDelimiter(ch))// 分隔符
		{
			Analy.Deli_Num++;
			output << ch;
			output << "\t";
			cout << ch << "\t\t" << "分隔符" << endl;
			if ((ch = fgetc(C_source)) == EOF) {
				finish = true;
				break;
			}
		}

		if (isMono(ch))
		{
			
				str[pos++] = ch;
				if ((ch = fgetc(C_source)) == EOF)
					finish = true;
				str[pos++] = ch;
			

			if (str[0] == '\'') {
				ch = fgetc(C_source);
				str[pos++] = ch;
				if(ch !='\'')
				{
					cout << "ERROR, NOT AN CHAR!!! lines:" << Analy.line + 1<< endl;	// 错误
					exit(0);
				}
				output << "'c'"; // 语法分析代表字符
				output << "\t";
				cout << str.substr(0, pos) << "\t\t" << "字符" << endl;
				ch = fgetc(C_source);
			}
			else if (finish == false && isBino(str.substr(0, pos)))
			{
				Analy.Bino_Num++;
				output << str.substr(0, pos)+"\t";
				cout << str.substr(0, pos) << "\t\t" << "双目运算符" << endl;
				ch = fgetc(C_source);
			}
			else
			{
				if (str[0] == '/' && str[1] == '/') {
					while (ch != '\n') {
						ch = fgetc(C_source);
						str[pos++] = ch;
					}
					cout << str.substr(0, 2) << "\t\t" << "注释" << endl;
				}
				else if (str[0] == '#')
				{
					int left;
					while (ch != '>') {
						if (ch == '<') left = pos;
						ch = fgetc(C_source);
						str[pos++] = ch;
					}
					cout << str.substr(left, pos - left - 1) 
						<< "\t\t" << "头文件" << endl;
					ch = fgetc(C_source);
				}
				else {
					Analy.Mono_Num++;
					output << str[0];
					output << "\t";
					cout << str[0] << "\t\t" << "单目运算符" << endl;
					ch = fgetc(C_source);
				}
			}
			Analy.char_Num += pos;
			pos = 0;
		}

		if (notRecog(ch))
		{
			cout << "ERROR, NOT RECOGNIZATION!!! lines:" << Analy.line + 1 << endl;	// 错误
			exit(0);
		}

		if (ch == ' ' || ch == '\t' || ch == '\n') {
			if (ch == '\n')
				Analy.line++;
			if ((ch = fgetc(C_source)) == EOF)
			{
				finish = true;
				break;
			}
			continue;
		}

		Analy.char_Num += pos;
	}
}

int main()
{
	C_source = fopen("..\\..\\源程序.txt", "r+");
	output.open("..\\..\\output语义分析.txt");
	scan_source();
	fclose(C_source);
	Analy.show();
}