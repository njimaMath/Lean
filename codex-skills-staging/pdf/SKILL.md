# Extract structured data from PDF files

Use Python to read PDFs and extract structured information from them.

Before you start, ask for the PDF file if it is not provided. Clarify the output format if the user's desired schema is not obvious.

Data extraction workflow:
1. Inspect the PDF to determine whether it is text-based, scanned, or mixed.
2. Choose the simplest reliable extraction approach:
   - Text-based: use `pdfplumber`, `pypdf`, or `PyMuPDF`
   - Scanned or image-heavy: use OCR with `ocrmypdf` or `pytesseract`
   - Tables: try `camelot`, `tabula-py`, or `pdfplumber` table extraction
3. Normalize the extracted data into the schema the user asked for.
4. Validate edge cases:
   - multi-page records
   - headers or footers repeated on every page
   - merged cells or broken rows in tables
   - rotated pages or mixed page sizes
5. Return both:
   - the structured result
   - a short note describing extraction assumptions or uncertain fields

Implementation notes:
- Prefer reproducible Python scripts over manual copy and paste.
- Keep raw extracted text separate from cleaned structured output when the task is complex.
- If OCR is needed, note that accuracy depends on scan quality.
- For large PDFs, process a page range first to verify the approach before scaling up.

Output formats you can produce:
- JSON
- CSV
- Markdown tables
- SQL insert statements
- Custom schemas the user provides
