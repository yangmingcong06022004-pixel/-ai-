from dotenv import load_dotenv
import os

load_dotenv()  # 自动读取 .env 文件

api_key = os.environ.get("DEEPSEEK_API_KEY")