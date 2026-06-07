# build_rag_csv.py
import pandas as pd

# 1. 读取清洗后的数据（英文）
df = pd.read_csv("cleaned_michelin.csv")
print(f"读取到 {len(df)} 条餐厅数据")
print("列名:", list(df.columns))

# 2. 构建文档列表
documents = []  # 每个元素是 (doc_id, content)

for idx, row in df.iterrows():
    # 安全处理缺失值
    def safe_str(val):
        return str(val) if pd.notna(val) else ''
    
    # 原有用到的字段：name, cuisine, price, address, description, facilitiesand
    # 你的数据里 address 列存在，location 列也有，但原代码用了 address，我们就用 address
    text = f"""Restaurant Name: {safe_str(row['name'])}
Cuisine: {safe_str(row['cuisine'])}
Price Level: {safe_str(row['price'])}
Address: {safe_str(row['address'])}
Description: {safe_str(row['description'])}
Facilities: {safe_str(row['facilitiesand'])}"""
    
    # 可选优化：添加星级和国家（不影响原有字段）
    if 'star_rating' in df.columns and pd.notna(row['star_rating']):
        text += f"\nMichelin Star: {int(row['star_rating'])} Star(s)"
    if 'country' in df.columns and pd.notna(row['country']):
        text += f"\nCountry: {safe_str(row['country'])}"
    
    # 文档 ID：可以用原有的“行号”列（如果存在且唯一），否则用 idx
    if '行号' in df.columns and pd.notna(row['行号']):
        doc_id = f"rest_{int(row['行号'])}"
    else:
        doc_id = f"rest_{idx}"
    
    documents.append((doc_id, text))

print(f"共生成了 {len(documents)} 个文档")
print("第一个文档示例：\n", documents[0][1] if documents else "无")

# 3. 保存为 CSV（方案 C）
df_docs = pd.DataFrame(documents, columns=["doc_id", "content"])
df_docs.to_csv("rag_documents.csv", index=False, encoding="utf-8")
print("\n✅ 已保存为 rag_documents.csv")
print("文件前两行预览：")
print(df_docs.head(2))