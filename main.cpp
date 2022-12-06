#include <any>
#include <iostream>
#include <map>
#include <memory>
#include <sstream>
#include <variant>
#include <vector>

#include "llvm/ADT/APFloat.h"
#include "llvm/ADT/Optional.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Verifier.h"
#include "llvm/MC/TargetRegistry.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Host.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Target/TargetMachine.h"
#include "llvm/Target/TargetOptions.h"

using namespace std;
using namespace llvm;

using StringIter = string::const_iterator;

static unique_ptr<LLVMContext> TheContext;
static unique_ptr<Module> TheModule;
static unique_ptr<IRBuilder<>> Builder;
static map<StringRef, Value*> NamedValues;

enum TokenType {
    Eof,
    Def,
    Extern,
    Ident,
    Number,
    BinOp,
    LParen,
    RParen,
    Comma,
    Unknown,
};

struct Token {
    Token() = delete;
    Token(TokenType type)
        : type(type)
    {
    }
    Token(double num)
        : type(Number)
        , m_data(num)
    {
    }
    Token(string ident)
        : type(Ident)
        , m_data(ident)
    {
    }
    Token(TokenType type, char c)
        : type(type)
        , m_data(c)
    {
    }

    TokenType getType() const
    {
        return type;
    }

    char getChar() const
    {
        return get<char>(m_data);
    }

    double getNumber() const
    {
        return get<double>(m_data);
    }

    string getIdent() const
    {
        return get<string>(m_data);
    }

private:
    variant<double, char, string> m_data;
    TokenType type;
};

static map<char, int> binopPrecedence = {
    { '<', 10 },
    { '+', 20 },
    { '-', 20 },
    { '*', 40 },
};

class Lexer {
public:
    Lexer(string source)
        : m_source(source)
        , m_iter(m_source.cbegin())
    {
    }

    vector<Token> tokenize()
    {
        vector<Token> tokens;
        while (true) {
            Token t = getNextToken();
            tokens.push_back(t);
            if (t.getType() == Eof)
                break;
        }
        return tokens;
    }

    Token getNextToken()
    {
        while (isspace(peek()))
            consume();
        if (m_iter == m_source.cend())
            return Token(Eof);
        else if (isalpha(peek())) {
            string str;
            do
                str += consume();
            while (isalpha(peek()));
            if (str == "def")
                return Token(Def);
            if (str == "extern")
                return Token(Extern);
            else
                return Token(str);
        } else if (isdigit(peek()) || peek() == '.') {
            string str;
            do
                str += consume();
            while (isdigit(peek()) || peek() == '.');
            return Token(stod(str));
        } else if (peek() == '#') {
            do
                consume();
            while (peek() != '\n');
            return getNextToken();
        } else if (binopPrecedence.find(peek()) != binopPrecedence.end()) {
            return Token(BinOp, consume());
        } else if (peek() == '(') {
            consume();
            return Token(LParen);
        } else if (peek() == ')') {
            consume();
            return Token(RParen);
        } else if (peek() == ',') {
            consume();
            return Token(Comma);
        } else {
            return Token(Unknown, consume());
        }
    }

    char peek()
    {
        if (m_iter != m_source.cend())
            return *m_iter;
        return 0;
    }

    char consume()
    {
        if (m_iter != m_source.cend())
            return *m_iter++;
        return 0;
    }

private:
    string m_source;
    StringIter m_iter;
};

class ASTNode {
public:
    virtual ~ASTNode() { }

    virtual string dump() { return ""; }
    virtual Value* codegen() = 0;
};

class ExprAST : public ASTNode {
public:
    virtual ~ExprAST() { }
    virtual Value* codegen() { return nullptr; }
};

class NumberExprAST : public ExprAST {
public:
    NumberExprAST(double value)
        : m_value(value)
    {
    }

    virtual string dump()
    {
        return "NumberExpr: " + to_string(m_value);
    }

    virtual Value* codegen()
    {
        return ConstantFP::get(*TheContext, APFloat(m_value));
    }

private:
    double m_value;
};

class VariableExprAST : public ExprAST {
public:
    VariableExprAST(const string& name)
        : m_name(name)
    {
    }

    virtual string dump()
    {
        return "VariableExprAST: " + m_name;
    }

    virtual Value* codegen()
    {
        Value* v = NamedValues[m_name];
        if (!v)
            cout << "Unknown variable name\n";
        return v;
    }

private:
    string m_name;
};

class BinaryExprAST : public ExprAST {
public:
    BinaryExprAST(char op, unique_ptr<ExprAST> lhs,
        unique_ptr<ExprAST> rhs)
        : m_op(op)
        , m_lhs(move(lhs))
        , m_rhs(move(rhs))
    {
    }

    virtual string dump() override
    {
        return "BinaryExprAST: "s + m_op + '\n' + m_lhs->dump() + '\n' + m_rhs->dump() + '\n';
    }

    virtual Value* codegen()
    {
        Value* L = m_lhs->codegen();
        Value* R = m_rhs->codegen();
        if (!L || !R)
            return nullptr;

        switch (m_op) {
        case '+':
            return Builder->CreateFAdd(L, R, "addtmp");
        case '-':
            return Builder->CreateFSub(L, R, "subtmp");
        case '*':
            return Builder->CreateFMul(L, R, "multmp");
        case '<':
            L = Builder->CreateFCmpULT(L, R, "cmptmp");
            // Convert bool 0/1 to double 0.0 or 1.0
            return Builder->CreateUIToFP(L, Type::getDoubleTy(*TheContext),
                "booltmp");
        default:
            cout << "invalid binary operator\n";
            return nullptr;
        }
    }

private:
    char m_op;
    unique_ptr<ExprAST> m_lhs, m_rhs;
};

class CallExprAST : public ExprAST {
public:
    CallExprAST(const string& func,
        vector<unique_ptr<ExprAST>> args)
        : m_func(func)
        , m_args(move(args))
    {
    }

    virtual string dump()
    {
        string res = "CallExprAST: " + m_func + '\n';
        for (auto& a : m_args) {
            res += a->dump() + '\n';
        }
        return res;
    }

    Value* codegen()
    {
        // Look up the name in the global module table.
        Function* CalleeF = TheModule->getFunction(m_func);
        if (!CalleeF) {
            cout << "Unknown function referenced\n";
            return nullptr;
        }

        // If argument mismatch error.
        if (CalleeF->arg_size() != m_args.size()) {
            cout << "Incorrect # arguments passed\n";
            return nullptr;
        }

        vector<Value*> ArgsV;
        for (unsigned i = 0, e = m_args.size(); i != e; ++i) {
            ArgsV.push_back(m_args[i]->codegen());
            if (!ArgsV.back())
                return nullptr;
        }

        return Builder->CreateCall(CalleeF, ArgsV, "calltmp");
    }

private:
    string m_func;
    vector<unique_ptr<ExprAST>> m_args;
};

class PrototypeAST : public ASTNode {
public:
    PrototypeAST(const string& name, vector<string> args)
        : m_name(name)
        , m_args(move(args))
    {
    }

    const string& getName() const { return m_name; }

    virtual string dump()
    {
        string res = "PrototypeAST: " + m_name + '\n';
        for (auto& a : m_args) {
            res += a + '\n';
        }
        return res;
    }

    Function* codegen()
    {
        // Make the function type:  double(double,double) etc.
        vector<Type*> Doubles(m_args.size(),
            Type::getDoubleTy(*TheContext));
        FunctionType* FT = FunctionType::get(Type::getDoubleTy(*TheContext), Doubles, false);

        Function* F = Function::Create(FT, Function::ExternalLinkage, m_name, TheModule.get());
        // Set names for all arguments.
        unsigned Idx = 0;
        for (auto& Arg : F->args())
            Arg.setName(m_args[Idx++]);
        return F;
    }

private:
    string m_name;
    vector<string> m_args;
};

class FunctionAST : public ASTNode {
public:
    FunctionAST(unique_ptr<PrototypeAST> proto,
        unique_ptr<ExprAST> body)
        : m_proto(move(proto))
        , m_body(move(body))
    {
    }

    virtual string dump()
    {
        return "FunctionAST:\n" + m_proto->dump() + '\n' + m_body->dump() + '\n';
    }

    Function* codegen()
    {
        // First, check for an existing function from a previous 'extern' declaration.
        Function* TheFunction = TheModule->getFunction(m_proto->getName());

        if (!TheFunction)
            TheFunction = m_proto->codegen();

        if (!TheFunction)
            return nullptr;

        if (!TheFunction->empty()) {
            cout << "Function cannot be redefined.\n";
            return nullptr;
        }

        // Create a new basic block to start insertion into.
        BasicBlock* BB = BasicBlock::Create(*TheContext, "entry", TheFunction);
        Builder->SetInsertPoint(BB);

        // Record the function arguments in the NamedValues map.
        NamedValues.clear();
        for (auto& Arg : TheFunction->args())
            NamedValues[Arg.getName()] = &Arg;

        if (Value* RetVal = m_body->codegen()) {
            // Finish off the function.
            Builder->CreateRet(RetVal);

            // Validate the generated code, checking for consistency.
            verifyFunction(*TheFunction);

            return TheFunction;
        }

        // Error reading body, remove function.
        TheFunction->eraseFromParent();
        return nullptr;
    }

private:
    unique_ptr<PrototypeAST> m_proto;
    unique_ptr<ExprAST> m_body;
};

using TokenIter = vector<Token>::const_iterator;

class Parser {
public:
    Parser(vector<Token> tokens)
        : m_tokens(move(tokens))
        , m_iter(m_tokens.cbegin())
    {
    }

    int getOpPrecedence(Token const& token)
    {
        if (token.getType() != BinOp) {
            return -1;
        }
        return binopPrecedence[token.getChar()] <= 0 ? -1 : binopPrecedence[token.getChar()];
    }

    // numberexpr ::= number
    unique_ptr<NumberExprAST> parseNumber()
    {
        return move(make_unique<NumberExprAST>(consume().getNumber()));
    }

    // parenexpr ::= '(' expression ')'
    unique_ptr<ExprAST> parseParenExpr()
    {
        consume();
        auto expr = parseExpr();
        if (!expr)
            return nullptr;
        if (peek().getType() != RParen) {
            cout << "Expected a ')'\n";
            return nullptr;
        }
        consume();
        return expr;
    }

    // identifierexpr
    //   ::= identifier
    //   ::= identifier '(' expression* ')'
    unique_ptr<ExprAST> parseIdentifierExpr()
    {
        auto ident = consume().getIdent();
        if (peek().getType() != LParen) {
            return make_unique<VariableExprAST>(ident);
        }
        consume();
        vector<unique_ptr<ExprAST>> args;
        if (peek().getType() != RParen) {
            while (true) {
                if (auto arg = parseExpr()) {
                    args.push_back(move(arg));
                } else {
                    return nullptr;
                }
                if (peek().getType() == RParen)
                    break;
                if (peek().getType() != Comma) {
                    cout << "Expected a ','\n";
                    return nullptr;
                }
                consume();
            }
        }
        consume();
        return make_unique<CallExprAST>(ident, move(args));
    }

    // primary
    //   ::= identifierexpr
    //   ::= numberexpr
    //   ::= parenexpr
    unique_ptr<ExprAST> parsePrimary()
    {
        switch (peek().getType()) {
        case Ident:
            return parseIdentifierExpr();
        case Number:
            return parseNumber();
        default:
            if (peek().getType() != LParen)
                return parseParenExpr();
            else {
                cout << "Unknown token\n";
                return nullptr;
            }
        }
    }

    /// binoprhs
    ///   ::= ('+' primary)*
    unique_ptr<ExprAST> parseBinOpRHS(int precedence, unique_ptr<ExprAST> lhs)
    {
        while (true) {
            int cur_precedence = getOpPrecedence(peek());
            if (cur_precedence < precedence)
                return lhs;

            auto op = consume().getChar();
            auto rhs = parsePrimary();
            if (!rhs)
                return nullptr;

            int next_precedence = getOpPrecedence(peek());
            if (cur_precedence < next_precedence) {
                rhs = parseBinOpRHS(cur_precedence + 1, move(rhs));
                if (!rhs)
                    return nullptr;
            }
            lhs = make_unique<BinaryExprAST>(op, move(lhs), move(rhs));
        }
    }

    /// expression
    ///   ::= primary binoprhs
    ///
    unique_ptr<ExprAST> parseExpr()
    {
        auto lhs = parsePrimary();
        if (!lhs)
            return nullptr;
        return parseBinOpRHS(0, move(lhs));
    }

    /// prototype
    ///   ::= id '(' id* ')'
    unique_ptr<PrototypeAST> parsePrototype()
    {
        if (peek().getType() != Ident) {
            cout << "Expected an identifier\n";
            return nullptr;
        }
        string name = consume().getIdent();
        if (peek().getType() != LParen) {
            cout << "Expected a '('\n";
            return nullptr;
        }
        consume();
        vector<string> args;
        while (true) {
            if (peek().getType() == Ident) {
                args.push_back(consume().getIdent());
                if (peek().getType() == Comma)
                    consume();
                else if (peek().getType() != RParen) {
                    cout << "Expected a ',' or a ')'\n";
                    return nullptr;
                }
            } else if (peek().getType() == RParen)
                break;
            else {
                cout << "Expected an argument or a ')'\n";
                return nullptr;
            }
        }
        consume();
        return make_unique<PrototypeAST>(name, move(args));
    }

    /// definition ::= 'def' prototype expression
    unique_ptr<FunctionAST> parseDefinition()
    {
        consume();
        auto proto = parsePrototype();
        if (!proto)
            return nullptr;

        if (auto expr = parseExpr())
            return make_unique<FunctionAST>(move(proto), move(expr));
        return nullptr;
    }

    /// external ::= 'extern' prototype
    unique_ptr<PrototypeAST> parseExtern()
    {
        consume();
        return parsePrototype();
    }

    /// toplevelexpr ::= expression
    unique_ptr<FunctionAST> ParseTopLevelExpr()
    {
        if (auto expr = parseExpr()) {
            auto proto = make_unique<PrototypeAST>("", vector<string>());
            return make_unique<FunctionAST>(move(proto), move(expr));
        }
        return nullptr;
    }

    /// top ::= definition | external | expression | ';'
    vector<unique_ptr<ASTNode>> parse()
    {
        vector<unique_ptr<ASTNode>> nodes;
        unique_ptr<ASTNode> node;
        while (peek().getType() != Eof) {
            switch (peek().getType()) {
            case Def:
                node = parseDefinition();
                break;
            case Extern:
                node = parseExtern();
                break;
            case Unknown:
                if (peek().getChar() == ';') {
                    consume();
                    continue;
                }
            default:
                node = ParseTopLevelExpr();
                break;
            }

            if (node) {
                nodes.push_back(move(node));
            } else {
                return {};
            }
        }
        return nodes;
    }

    Token const peek()
    {
        if (m_iter != m_tokens.cend())
            return *m_iter;
        return Token(Eof);
    }

    Token const consume()
    {
        if (m_iter != m_tokens.cend())
            return *m_iter++;
        return Token(Eof);
    }

private:
    vector<Token> m_tokens;
    TokenIter m_iter;
};

static void InitializeModule()
{
    // Open a new context and module.
    TheContext = make_unique<LLVMContext>();
    TheModule = make_unique<Module>("my own kaleidoscope", *TheContext);

    // Create a new builder for the module.
    Builder = make_unique<IRBuilder<>>(*TheContext);

    InitializeAllTargetInfos();
    InitializeAllTargets();
    InitializeAllTargetMCs();
    InitializeAllAsmParsers();
    InitializeAllAsmPrinters();
}

int main()
{
    InitializeModule();
    stringstream ss;
    ss << cin.rdbuf();
    string source = ss.str();
    Lexer l(move(source));
    auto tokens = l.tokenize();
    Parser p(tokens);
    auto ast = p.parse();
    if (ast.empty()) {
        return 1;
    }

    for (auto& node : ast) {
        if (node) {
            cout << node->dump() << '\n';
            node->codegen();
        }
    }
    TheModule->print(errs(), nullptr);

    auto TargetTriple = sys::getDefaultTargetTriple();
    std::string Error;

    auto Target = TargetRegistry::lookupTarget(TargetTriple, Error);
    auto CPU = "generic";
    auto Features = "";

    TargetOptions opt;
    auto RM = Optional<Reloc::Model>();
    auto TargetMachine = Target->createTargetMachine(TargetTriple, CPU, Features, opt, RM);

    TheModule->setDataLayout(TargetMachine->createDataLayout());
    TheModule->setTargetTriple(TargetTriple);
    auto Filename = "output.o";
    std::error_code EC;
    raw_fd_ostream dest(Filename, EC, sys::fs::OF_None);

    if (EC) {
        errs() << "Could not open file: " << EC.message();
        return 1;
    }
    legacy::PassManager pass;
    auto FileType = CGFT_ObjectFile;

    if (TargetMachine->addPassesToEmitFile(pass, dest, nullptr, FileType)) {
        errs() << "TargetMachine can't emit a file of this type";
        return 1;
    }

    pass.run(*TheModule);
    dest.flush();

    return 0;
}
