import pandas as pd
import os
from langchain_community.document_loaders import DataFrameLoader
from langchain_community.vectorstores import Chroma
from langchain_community.embeddings import HuggingFaceEmbeddings
from langchain.chains import RetrievalQA
from langchain_openai import ChatOpenAI  # 注意：新版用 langchain_openai

# ================= 配置 =================
# 填入你的 DeepSeek API Key（从 deepseek api key management.py 里拿）
DEEPSEEK_API_KEY = "sk-c21c69376a4a43568ab2d69d049deaa0"   # 替换成真实 key
DEEPSEEK_BASE_URL = "https://api.deepseek.com/v1"
# ========================================

def build_vectorstore(csv_path="rag_documents.csv", persist_dir="chroma_db"):
    """读取 CSV，建立向量数据库（如果已存在则直接加载）"""
    if os.path.exists(persist_dir) and os.listdir(persist_dir):
        print("发现已有向量数据库，直接加载...")
        embedding_model = HuggingFaceEmbeddings(
            model_name="BAAI/bge-m3",
            model_kwargs={'device': 'cpu'},
            encode_kwargs={'normalize_embeddings': True}
        )
        vectorstore = Chroma(persist_directory=persist_dir, embedding_function=embedding_model)
        return vectorstore
    
    print("首次运行，构建向量数据库（需要下载模型 ~2.2GB，第一次较慢）...")
    df = pd.read_csv(csv_path)
    loader = DataFrameLoader(df, page_content_column="content")
    docs = loader.load()
    # 把 doc_id 作为 metadata
    for i, doc in enumerate(docs):
        doc.metadata["doc_id"] = df.iloc[i]["doc_id"]
    
    embedding_model = HuggingFaceEmbeddings(
        model_name="BAAI/bge-m3",
        model_kwargs={'device': 'cpu'},
        encode_kwargs={'normalize_embeddings': True}
    )
    vectorstore = Chroma.from_documents(
        documents=docs,
        embedding=embedding_model,
        persist_directory=persist_dir
    )
    vectorstore.persist()
    print(f"向量数据库已建立，共 {len(docs)} 条文档，保存在 {persist_dir}")
    return vectorstore

def create_qa_chain(vectorstore):
    """创建检索 + 问答链，使用 DeepSeek API"""
    llm = ChatOpenAI(
        model="deepseek-chat",               # DeepSeek 模型名
        openai_api_key=DEEPSEEK_API_KEY,
        openai_api_base=DEEPSEEK_BASE_URL,
        temperature=0.2,
        max_tokens=1024
    )
    retriever = vectorstore.as_retriever(search_kwargs={"k": 5})
    qa_chain = RetrievalQA.from_chain_type(
        llm=llm,
        chain_type="stuff",
        retriever=retriever,
        return_source_documents=True,
        verbose=False
    )
    return qa_chain

def main():
    print("正在加载 RAG 系统...")
    vectorstore = build_vectorstore()
    qa_chain = create_qa_chain(vectorstore)
    print("系统就绪！输入问题（中英文均可），输入 quit 退出。")
    while True:
        query = input("\n你的问题：")
        if query.lower() in ["quit", "exit", "q"]:
            break
        result = qa_chain.invoke({"query": query})
        print("\n【回答】")
        print(result['result'])
        print("\n【参考餐厅】")
        for i, doc in enumerate(result['source_documents']):
            print(f"{i+1}. {doc.metadata.get('doc_id', 'unknown')} - {doc.page_content[:100]}...")

if __name__ == "__main__":
    main()