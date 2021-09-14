import re
from urllib.parse import urljoin
from urllib.request import urlretrieve as download

import requests
from bs4 import BeautifulSoup

lectures = "https://pirsa.org/C19007?page="
for i in range(3):
    html_paginated = BeautifulSoup(requests.get(lectures + str(i)).text, "html.parser")
    for link in html_paginated.select("article > div.content-second > h2 > a"):
        lecture_num = re.search(r"\d+", link.find("span").text)[0]
        if int(lecture_num) < 10:
            lecture_num = f"0{lecture_num}"

        lecture_page = urljoin("https://pirsa.org", link["href"])
        lecture_page_html = BeautifulSoup(
            requests.get(lecture_page).text, "html.parser"
        )
        video_url = lecture_page_html.find("source")["src"]
        print(f"Downloading lecture {lecture_num} from {video_url}")
        download(video_url, f"./lectures/lec-{lecture_num}.mp4")
