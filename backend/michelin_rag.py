import os
import pandas as pd
from langchain_community.vectorstores import Chroma
from langchain_community.embeddings import HuggingFaceEmbeddings
from langchain_openai import ChatOpenAI
from langchain_core.prompts import PromptTemplate
from langchain_core.output_parsers import StrOutputParser
from langchain_core.runnables import RunnablePassthrough

DEEPSEEK_API_KEY  = os.environ.get("DEEPSEEK_API_KEY", "")
DEEPSEEK_BASE_URL = "https://api.deepseek.com/v1"
VECTOR_DB_DIR     = "chroma_db"
CSV_PATH          = "rag_documents.csv"   # ⚠️ 确保这个文件存在，并且有 content 和 doc_id 列

retriever = None
rag_chain = None

PROMPT_TEMPLATE = """你是米其林餐厅专家助手。根据以下参考资料回答用户问题。
如果参考资料中没有相关信息，请如实说明。回答要具体，包含餐厅名称、星级、地址等信息。

参考资料：
{context}

用户问题：{question}

回答："""

def load_rag():
    global retriever, rag_chain
    print("📦 加载 RAG 系统...")
    
    # 1. 嵌入模型（首次运行会自动下载 bge-m3）
    embedding = HuggingFaceEmbeddings(
        model_name="BAAI/bge-m3",
        model_kwargs={'device': 'cpu'},
        encode_kwargs={'normalize_embeddings': True}
    )
    
    # 2. 向量库存在？不存在则从 CSV 构建
    if not os.path.exists(VECTOR_DB_DIR) or not os.listdir(VECTOR_DB_DIR):
        print("未找到向量库，从 CSV 构建中...")
        from langchain_community.document_loaders import DataFrameLoader
        df = pd.read_csv(CSV_PATH)
        # 必须包含 'content' 列（文档内容）和 'doc_id' 列（唯一标识）
        loader = DataFrameLoader(df, page_content_column="content")
        docs = loader.load()
        for i, doc in enumerate(docs):
            doc.metadata["doc_id"] = str(df.iloc[i]["doc_id"])
        vectorstore = Chroma.from_documents(docs, embedding, persist_directory=VECTOR_DB_DIR)
        print("✅ 向量库构建完成")
    else:
        vectorstore = Chroma(persist_directory=VECTOR_DB_DIR, embedding_function=embedding)
        print("✅ 加载已有向量库")
    
    retriever = vectorstore.as_retriever(search_kwargs={"k": 5})
    
    # 3. LLM（通过 DeepSeek API）
    llm = ChatOpenAI(
        model="deepseek-chat",
        openai_api_key=DEEPSEEK_API_KEY,
        openai_api_base=DEEPSEEK_BASE_URL,
        temperature=0.2,
        max_tokens=1024
    )
    
    prompt = PromptTemplate(
        input_variables=["context", "question"],
        template=PROMPT_TEMPLATE
    )
    
    rag_chain = (
        {"context": retriever, "question": RunnablePassthrough()}
        | prompt | llm | StrOutputParser()
    )
    print("✅ RAG 系统加载完成")

def ask_michelin(question: str) -> dict:
    global retriever, rag_chain
    if rag_chain is None:
        load_rag()
    answer = rag_chain.invoke(question)
    source_docs = retriever.invoke(question)
    references = [doc.metadata.get("doc_id", "unknown") for doc in source_docs]
    return {"answer": answer, "references": references}