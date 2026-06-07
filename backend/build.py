from langchain_community.document_loaders import CSVLoader
from langchain_community.vectorstores import Chroma
from langchain_community.embeddings import HuggingFaceEmbeddings
import math

# 1. 加载CSV数据
print("正在加载CSV...")
loader = CSVLoader("rag_documents.csv", encoding="utf-8")
documents = loader.load()
print(f"✅ 共加载 {len(documents)} 条餐厅数据")

# 2. 【关键】全程只用all-MiniLM-L6-v2，384维固定输出，绝对不会再维度不匹配
embedding = HuggingFaceEmbeddings(model_name="all-MiniLM-L6-v2")

# 3. 分批构建向量库（每批5000条，避开Chroma批次上限）
batch_size = 5000
total_batches = math.ceil(len(documents) / batch_size)

print(f"开始构建向量库，共分 {total_batches} 批插入...")

db = None
for i in range(total_batches):
    start_idx = i * batch_size
    end_idx = (i + 1) * batch_size
    batch_docs = documents[start_idx:end_idx]
    
    print(f"正在插入第 {i+1}/{total_batches} 批，共 {len(batch_docs)} 条数据...")
    
    if i == 0:
        db = Chroma.from_documents(
            documents=batch_docs,
            embedding=embedding,
            persist_directory="./chroma_db"
        )
    else:
        db.add_documents(documents=batch_docs)
    
    db.persist()

db.persist()
print(f"\n🎉 向量库构建完成！维度384，共 {len(documents)} 条数据，已保存到chroma_db")