You ran a pre-v8 version. Image support only exists from v8 onward. v7 and earlier treat that URL as HTML, try to parse JPEG bytes as a webpage, and produce nothing. Check the top of the file you're running, or just use scraper_v9.py from here on — it's the one with every fix from today.
OCR isn't installed on your machine. You need both the Python packages and the engine:
pip install pytesseract pillow
   sudo apt install tesseract-ocr        # or: brew install tesseract (Mac)
  
