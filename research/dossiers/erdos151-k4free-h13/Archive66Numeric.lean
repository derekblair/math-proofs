import Archive66Cert0
import Archive66Cert1
import Archive66Cert2
import Archive66Cert3
import Archive66Cert4
import Archive66Cert5
import Archive66Cert6
import Archive66Cert7
import Archive66Cert8
import Archive66Cert9
import Archive66Cert10
import Archive66Cert11
import Archive66Cert12
import Archive66Cert13
import Archive66Cert14
import Archive66Cert15
import Archive66Cert16
import Archive66Cert17
import Archive66Cert18
import Archive66Cert19
import Archive66Cert20
namespace Erdos151Ramsey.Archive66
set_option maxRecDepth 8192
set_option maxHeartbeats 0
def p3 : Plan := .step 20 p4 p11
theorem c3 : check p3 51047146331477510586 11 = true := check_combine (v := 20) (l := p4) (r := p11) (m := 51047146331477510586) (k := 11) (by decide +kernel) c4 c11

def p218 : Plan := .step 62 p219 p226
theorem c218 : check p218 51069115126243658267 12 = true := check_combine (v := 62) (l := p219) (r := p226) (m := 51069115126243658267) (k := 12) (by decide +kernel) c219 c226

def p208 : Plan := .step 17 p209 p218
theorem c208 : check p208 51069115126243789339 12 = true := check_combine (v := 17) (l := p209) (r := p218) (m := 51069115126243789339) (k := 12) (by decide +kernel) c209 c218

def p198 : Plan := .step 5 p199 p208
theorem c198 : check p198 51069115126243789371 12 = true := check_combine (v := 5) (l := p199) (r := p208) (m := 51069115126243789371) (k := 12) (by decide +kernel) c199 c208

def p180 : Plan := .step 8 p181 p198
theorem c180 : check p180 51069115126243789627 12 = true := check_combine (v := 8) (l := p181) (r := p198) (m := 51069115126243789627) (k := 12) (by decide +kernel) c181 c198

def p168 : Plan := .step 7 p169 p180
theorem c168 : check p168 51069115126243789755 12 = true := check_combine (v := 7) (l := p169) (r := p180) (m := 51069115126243789755) (k := 12) (by decide +kernel) c169 c180

def p148 : Plan := .step 54 p149 p168
theorem c148 : check p148 51087129524753271739 12 = true := check_combine (v := 54) (l := p149) (r := p168) (m := 51087129524753271739) (k := 12) (by decide +kernel) c149 c168

def p122 : Plan := .step 49 p123 p148
theorem c122 : check p122 51087692474706693051 12 = true := check_combine (v := 49) (l := p123) (r := p148) (m := 51087692474706693051) (k := 12) (by decide +kernel) c123 c148

def p90 : Plan := .step 42 p91 p122
theorem c90 : check p90 51087696872753204155 12 = true := check_combine (v := 42) (l := p91) (r := p122) (m := 51087696872753204155) (k := 12) (by decide +kernel) c91 c122

def p54 : Plan := .step 20 p55 p90
theorem c54 : check p54 51087696872754252731 12 = true := check_combine (v := 20) (l := p55) (r := p90) (m := 51087696872754252731) (k := 12) (by decide +kernel) c55 c90

def p2 : Plan := .step 10 p3 p54
theorem c2 : check p2 51087696872754253755 12 = true := check_combine (v := 10) (l := p3) (r := p54) (m := 51087696872754253755) (k := 12) (by decide +kernel) c3 c54

def p275 : Plan := .step 46 p276 p283
theorem c275 : check p275 52187678002594548096 11 = true := check_combine (v := 46) (l := p276) (r := p283) (m := 52187678002594548096) (k := 11) (by decide +kernel) c276 c283

def p327 : Plan := .step 47 p328 p345
theorem c327 : check p327 51913812749582699928 11 = true := check_combine (v := 47) (l := p328) (r := p345) (m := 51913812749582699928) (k := 11) (by decide +kernel) c328 c345

def p562 : Plan := .step 20 p563 p572
theorem c562 : check p562 51894179870562813208 12 = true := check_combine (v := 20) (l := p563) (r := p572) (m := 51894179870562813208) (k := 12) (by decide +kernel) c563 c572

def p554 : Plan := .step 11 p555 p562
theorem c554 : check p554 51894179870562815256 12 = true := check_combine (v := 11) (l := p555) (r := p562) (m := 51894179870562815256) (k := 12) (by decide +kernel) c555 c562

def p542 : Plan := .step 52 p543 p554
theorem c542 : check p542 51898683470190185752 12 = true := check_combine (v := 52) (l := p543) (r := p554) (m := 51898683470190185752) (k := 12) (by decide +kernel) c543 c554

def p522 : Plan := .step 42 p523 p542
theorem c522 : check p522 51898687868236696856 12 = true := check_combine (v := 42) (l := p523) (r := p542) (m := 51898687868236696856) (k := 12) (by decide +kernel) c523 c542

def p508 : Plan := .step 54 p509 p522
theorem c508 : check p508 51916702266746178840 12 = true := check_combine (v := 54) (l := p509) (r := p522) (m := 51916702266746178840) (k := 12) (by decide +kernel) c509 c522

def p480 : Plan := .step 49 p481 p508
theorem c480 : check p480 51917265216699600152 12 = true := check_combine (v := 49) (l := p481) (r := p508) (m := 51917265216699600152) (k := 12) (by decide +kernel) c481 c508

def p452 : Plan := .step 47 p453 p480
theorem c452 : check p452 51917405954187955480 12 = true := check_combine (v := 47) (l := p453) (r := p480) (m := 51917405954187955480) (k := 12) (by decide +kernel) c453 c480

def p420 : Plan := .step 46 p421 p452
theorem c420 : check p420 51917476322932133144 12 = true := check_combine (v := 46) (l := p421) (r := p452) (m := 51917476322932133144) (k := 12) (by decide +kernel) c421 c452

def p384 : Plan := .step 7 p385 p420
theorem c384 : check p384 51917476322932133272 12 = true := check_combine (v := 7) (l := p385) (r := p420) (m := 51917476322932133272) (k := 12) (by decide +kernel) c385 c420

def p326 : Plan := .step 58 p327 p384
theorem c326 : check p326 52205706699083845016 12 = true := check_combine (v := 58) (l := p327) (r := p384) (m := 52205706699083845016) (k := 12) (by decide +kernel) c327 c384

def p274 : Plan := .step 9 p275 p326
theorem c274 : check p274 52205706699083845528 12 = true := check_combine (v := 9) (l := p275) (r := p326) (m := 52205706699083845528) (k := 12) (by decide +kernel) c275 c326

def p790 : Plan := .step 16 p791 p804
theorem c790 : check p790 15011853274877508099 12 = true := check_combine (v := 16) (l := p791) (r := p804) (m := 15011853274877508099) (k := 12) (by decide +kernel) c791 c804

def p784 : Plan := .step 49 p785 p790
theorem c784 : check p784 15012416224830929411 12 = true := check_combine (v := 49) (l := p785) (r := p790) (m := 15012416224830929411) (k := 12) (by decide +kernel) c785 c790

def p774 : Plan := .step 39 p775 p784
theorem c774 : check p774 15012416774586743299 12 = true := check_combine (v := 39) (l := p775) (r := p784) (m := 15012416774586743299) (k := 12) (by decide +kernel) c775 c784

def p758 : Plan := .step 37 p759 p774
theorem c758 : check p758 15012416912025696771 12 = true := check_combine (v := 37) (l := p759) (r := p774) (m := 15012416912025696771) (k := 12) (by decide +kernel) c759 c774

def p748 : Plan := .step 25 p749 p758
theorem c748 : check p748 15012416912059251203 12 = true := check_combine (v := 25) (l := p749) (r := p758) (m := 15012416912059251203) (k := 12) (by decide +kernel) c749 c758

def p718 : Plan := .step 3 p719 p748
theorem c718 : check p718 15012416912059251211 12 = true := check_combine (v := 3) (l := p719) (r := p748) (m := 15012416912059251211) (k := 12) (by decide +kernel) c719 c748

def p702 : Plan := .step 58 p703 p718
theorem c702 : check p702 15300647288210962955 12 = true := check_combine (v := 58) (l := p703) (r := p718) (m := 15300647288210962955) (k := 12) (by decide +kernel) c703 c718

def p682 : Plan := .step 10 p683 p702
theorem c682 : check p682 15300647288210963979 12 = true := check_combine (v := 10) (l := p683) (r := p702) (m := 15300647288210963979) (k := 12) (by decide +kernel) c683 c702

def p660 : Plan := .step 65 p661 p682
theorem c660 : check p660 52194135435630067211 12 = true := check_combine (v := 65) (l := p661) (r := p682) (m := 52194135435630067211) (k := 12) (by decide +kernel) c661 c682

def p636 : Plan := .step 8 p637 p660
theorem c636 : check p636 52194135435630067467 12 = true := check_combine (v := 8) (l := p637) (r := p660) (m := 52194135435630067467) (k := 12) (by decide +kernel) c637 c660

def p612 : Plan := .step 42 p613 p636
theorem c612 : check p612 52194139833676578571 12 = true := check_combine (v := 42) (l := p613) (r := p636) (m := 52194139833676578571) (k := 12) (by decide +kernel) c613 c636

def p978 : Plan := .step 13 p979 p988
theorem c978 : check p978 9276694661111261187 12 = true := check_combine (v := 13) (l := p979) (r := p988) (m := 9276694661111261187) (k := 12) (by decide +kernel) c979 c988

def p974 : Plan := .step 60 p975 p978
theorem c974 : check p974 10429616165718108163 12 = true := check_combine (v := 60) (l := p975) (r := p978) (m := 10429616165718108163) (k := 12) (by decide +kernel) c975 c978

def p968 : Plan := .step 12 p969 p974
theorem c968 : check p968 10429616165718112259 12 = true := check_combine (v := 12) (l := p969) (r := p974) (m := 10429616165718112259) (k := 12) (by decide +kernel) c969 c974

def p962 : Plan := .step 65 p963 p968
theorem c962 : check p962 47323104313137215491 12 = true := check_combine (v := 65) (l := p963) (r := p968) (m := 47323104313137215491) (k := 12) (by decide +kernel) c963 c968

def p956 : Plan := .step 62 p957 p962
theorem c956 : check p956 51934790331564603395 12 = true := check_combine (v := 62) (l := p957) (r := p962) (m := 51934790331564603395) (k := 12) (by decide +kernel) c957 c962

def p944 : Plan := .step 58 p945 p956
theorem c944 : check p944 52223020707716315139 12 = true := check_combine (v := 58) (l := p945) (r := p956) (m := 52223020707716315139) (k := 12) (by decide +kernel) c945 c956

def p934 : Plan := .step 47 p935 p944
theorem c934 : check p934 52223161445204670467 12 = true := check_combine (v := 47) (l := p935) (r := p944) (m := 52223161445204670467) (k := 12) (by decide +kernel) c935 c944

def p916 : Plan := .step 16 p917 p934
theorem c916 : check p916 52223161445204736003 12 = true := check_combine (v := 16) (l := p917) (r := p934) (m := 52223161445204736003) (k := 12) (by decide +kernel) c917 c934

def p890 : Plan := .step 8 p891 p916
theorem c890 : check p890 52223161445204736259 12 = true := check_combine (v := 8) (l := p891) (r := p916) (m := 52223161445204736259) (k := 12) (by decide +kernel) c891 c916

def p870 : Plan := .step 49 p871 p890
theorem c870 : check p870 52223724395158157571 12 = true := check_combine (v := 49) (l := p871) (r := p890) (m := 52223724395158157571) (k := 12) (by decide +kernel) c871 c890

def p840 : Plan := .step 20 p841 p870
theorem c840 : check p840 52223724395159206147 12 = true := check_combine (v := 20) (l := p841) (r := p870) (m := 52223724395159206147) (k := 12) (by decide +kernel) c841 c870

def p1188 : Plan := .step 27 p1189 p1200
theorem c1188 : check p1188 38649766129168517395 12 = true := check_combine (v := 27) (l := p1189) (r := p1200) (m := 38649766129168517395) (k := 12) (by decide +kernel) c1189 c1200

def p1172 : Plan := .step 12 p1173 p1188
theorem c1172 : check p1172 38649766129168521491 12 = true := check_combine (v := 12) (l := p1173) (r := p1188) (m := 38649766129168521491) (k := 12) (by decide +kernel) c1173 c1188

def p1152 : Plan := .step 10 p1153 p1172
theorem c1152 : check p1152 38649766129168522515 12 = true := check_combine (v := 10) (l := p1153) (r := p1172) (m := 38649766129168522515) (k := 12) (by decide +kernel) c1153 c1172

def p1136 : Plan := .step 62 p1137 p1152
theorem c1136 : check p1136 43261452147595910419 12 = true := check_combine (v := 62) (l := p1137) (r := p1152) (m := 43261452147595910419) (k := 12) (by decide +kernel) c1137 c1152

def p1120 : Plan := .step 19 p1121 p1136
theorem c1120 : check p1120 43261452147596434707 12 = true := check_combine (v := 19) (l := p1121) (r := p1136) (m := 43261452147596434707) (k := 12) (by decide +kernel) c1121 c1136

def p1096 : Plan := .step 25 p1097 p1120
theorem c1096 : check p1096 43261452147629989139 12 = true := check_combine (v := 25) (l := p1097) (r := p1120) (m := 43261452147629989139) (k := 12) (by decide +kernel) c1097 c1120

def p1078 : Plan := .step 37 p1079 p1096
theorem c1078 : check p1078 43261452285068942611 12 = true := check_combine (v := 37) (l := p1079) (r := p1096) (m := 43261452285068942611) (k := 12) (by decide +kernel) c1079 c1096

def p1034 : Plan := .step 22 p1035 p1078
theorem c1034 : check p1034 43261452285073136915 12 = true := check_combine (v := 22) (l := p1035) (r := p1078) (m := 43261452285073136915) (k := 12) (by decide +kernel) c1035 c1078

def p1336 : Plan := .step 51 p1337 p1342
theorem c1336 : check p1336 10718559986335909913 12 = true := check_combine (v := 51) (l := p1337) (r := p1342) (m := 10718559986335909913) (k := 12) (by decide +kernel) c1337 c1342

def p1330 : Plan := .step 26 p1331 p1336
theorem c1330 : check p1330 10718559986403018777 12 = true := check_combine (v := 26) (l := p1331) (r := p1336) (m := 10718559986403018777) (k := 12) (by decide +kernel) c1331 c1336

def p1316 : Plan := .step 19 p1317 p1330
theorem c1316 : check p1316 10718559986403543065 12 = true := check_combine (v := 19) (l := p1317) (r := p1330) (m := 10718559986403543065) (k := 12) (by decide +kernel) c1317 c1330

def p1306 : Plan := .step 25 p1307 p1316
theorem c1306 : check p1306 10718559986437097497 12 = true := check_combine (v := 25) (l := p1307) (r := p1316) (m := 10718559986437097497) (k := 12) (by decide +kernel) c1307 c1316

def p1286 : Plan := .step 10 p1287 p1306
theorem c1286 : check p1286 10718559986437098521 12 = true := check_combine (v := 10) (l := p1287) (r := p1306) (m := 10718559986437098521) (k := 12) (by decide +kernel) c1287 c1306

def p1262 : Plan := .step 65 p1263 p1286
theorem c1262 : check p1262 47612048133856201753 12 = true := check_combine (v := 65) (l := p1263) (r := p1286) (m := 47612048133856201753) (k := 12) (by decide +kernel) c1263 c1286

def p1248 : Plan := .step 62 p1249 p1262
theorem c1248 : check p1248 52223734152283589657 12 = true := check_combine (v := 62) (l := p1249) (r := p1262) (m := 52223734152283589657) (k := 12) (by decide +kernel) c1249 c1262

def p1472 : Plan := .step 10 p1473 p1486
theorem c1472 : check p1472 2050788766506921243 12 = true := check_combine (v := 10) (l := p1473) (r := p1486) (m := 2050788766506921243) (k := 12) (by decide +kernel) c1473 c1486

def p1466 : Plan := .step 27 p1467 p1472
theorem c1466 : check p1466 2050788766641138971 12 = true := check_combine (v := 27) (l := p1467) (r := p1472) (m := 2050788766641138971) (k := 12) (by decide +kernel) c1467 c1472

def p1448 : Plan := .step 12 p1449 p1466
theorem c1448 : check p1448 2050788766641143067 12 = true := check_combine (v := 12) (l := p1449) (r := p1466) (m := 2050788766641143067) (k := 12) (by decide +kernel) c1449 c1466

def p1436 : Plan := .step 19 p1437 p1448
theorem c1436 : check p1436 2050788766641667355 12 = true := check_combine (v := 19) (l := p1437) (r := p1448) (m := 2050788766641667355) (k := 12) (by decide +kernel) c1437 c1448

def p1424 : Plan := .step 62 p1425 p1436
theorem c1424 : check p1424 6662474785069055259 12 = true := check_combine (v := 62) (l := p1425) (r := p1436) (m := 6662474785069055259) (k := 12) (by decide +kernel) c1425 c1436

def p1398 : Plan := .step 51 p1399 p1424
theorem c1398 : check p1398 6664726584882740507 12 = true := check_combine (v := 51) (l := p1399) (r := p1424) (m := 6664726584882740507) (k := 12) (by decide +kernel) c1399 c1424

def p1388 : Plan := .step 25 p1389 p1398
theorem c1388 : check p1388 6664726584916294939 12 = true := check_combine (v := 25) (l := p1389) (r := p1398) (m := 6664726584916294939) (k := 12) (by decide +kernel) c1389 c1398

def p1552 : Plan := .step 47 p1553 p1572
theorem c1552 : check p1552 47587471855253175562 12 = true := check_combine (v := 47) (l := p1553) (r := p1572) (m := 47587471855253175562) (k := 12) (by decide +kernel) c1553 c1572

def p1542 : Plan := .step 19 p1543 p1552
theorem c1542 : check p1542 47587471855253699850 12 = true := check_combine (v := 19) (l := p1543) (r := p1552) (m := 47587471855253699850) (k := 12) (by decide +kernel) c1543 c1552

def p1522 : Plan := .step 0 p1523 p1542
theorem c1522 : check p1522 47587471855253699851 12 = true := check_combine (v := 0) (l := p1523) (r := p1542) (m := 47587471855253699851) (k := 12) (by decide +kernel) c1523 c1542

def p1664 : Plan := .step 0 p1665 p1674
theorem c1664 : check p1664 9272143097465650187 12 = true := check_combine (v := 0) (l := p1665) (r := p1674) (m := 9272143097465650187) (k := 12) (by decide +kernel) c1665 c1674

def p1648 : Plan := .step 44 p1649 p1664
theorem c1648 : check p1648 9272160689651694603 12 = true := check_combine (v := 44) (l := p1649) (r := p1664) (m := 9272160689651694603) (k := 12) (by decide +kernel) c1649 c1664

def p1640 : Plan := .step 52 p1641 p1648
theorem c1640 : check p1640 9276664289279065099 12 = true := check_combine (v := 52) (l := p1641) (r := p1648) (m := 9276664289279065099) (k := 12) (by decide +kernel) c1641 c1648

def p1632 : Plan := .step 39 p1633 p1640
theorem c1632 : check p1632 9276664839034878987 12 = true := check_combine (v := 39) (l := p1633) (r := p1640) (m := 9276664839034878987) (k := 12) (by decide +kernel) c1633 c1640

def p1622 : Plan := .step 8 p1623 p1632
theorem c1622 : check p1622 9276664839034879243 12 = true := check_combine (v := 8) (l := p1623) (r := p1632) (m := 9276664839034879243) (k := 12) (by decide +kernel) c1623 c1632

def p1610 : Plan := .step 47 p1611 p1622
theorem c1610 : check p1610 9276805576523234571 12 = true := check_combine (v := 47) (l := p1611) (r := p1622) (m := 9276805576523234571) (k := 12) (by decide +kernel) c1611 c1622

def p1770 : Plan := .step 51 p1771 p1788
theorem c1770 : check p1770 38680375985281938457 12 = true := check_combine (v := 51) (l := p1771) (r := p1788) (m := 38680375985281938457) (k := 12) (by decide +kernel) c1771 c1788

def p1760 : Plan := .step 63 p1761 p1770
theorem c1760 : check p1760 47903748022136714265 12 = true := check_combine (v := 63) (l := p1761) (r := p1770) (m := 47903748022136714265) (k := 12) (by decide +kernel) c1761 c1770

def p1742 : Plan := .step 53 p1743 p1760
theorem c1742 : check p1742 47912755221391455257 12 = true := check_combine (v := 53) (l := p1743) (r := p1760) (m := 47912755221391455257) (k := 12) (by decide +kernel) c1743 c1760

def p1718 : Plan := .step 58 p1719 p1742
theorem c1718 : check p1718 48200985597543167001 12 = true := check_combine (v := 58) (l := p1719) (r := p1742) (m := 48200985597543167001) (k := 12) (by decide +kernel) c1719 c1742

def p1878 : Plan := .step 52 p1879 p1888
theorem c1878 : check p1878 1789579989935630362 12 = true := check_combine (v := 52) (l := p1879) (r := p1888) (m := 1789579989935630362) (k := 12) (by decide +kernel) c1879 c1888

def p1866 : Plan := .step 12 p1867 p1878
theorem c1866 : check p1866 1789579989935634458 12 = true := check_combine (v := 12) (l := p1867) (r := p1878) (m := 1789579989935634458) (k := 12) (by decide +kernel) c1867 c1878

def p1854 : Plan := .step 53 p1855 p1866
theorem c1854 : check p1854 1798587189190375450 12 = true := check_combine (v := 53) (l := p1855) (r := p1866) (m := 1798587189190375450) (k := 12) (by decide +kernel) c1855 c1866

def p1834 : Plan := .step 51 p1835 p1854
theorem c1834 : check p1834 1800838989004060698 12 = true := check_combine (v := 51) (l := p1835) (r := p1854) (m := 1800838989004060698) (k := 12) (by decide +kernel) c1835 c1854

def p1948 : Plan := .step 26 p1949 p1958
theorem c1948 : check p1948 2041675998772308250 12 = true := check_combine (v := 26) (l := p1949) (r := p1958) (m := 2041675998772308250) (k := 12) (by decide +kernel) c1949 c1958

def p1932 : Plan := .step 10 p1933 p1948
theorem c1932 : check p1932 2041675998772309274 12 = true := check_combine (v := 10) (l := p1933) (r := p1948) (m := 2041675998772309274) (k := 12) (by decide +kernel) c1933 c1948

def p2038 : Plan := .step 26 p2039 p2050
theorem c2038 : check p2038 48147254661702201626 12 = true := check_combine (v := 26) (l := p2039) (r := p2050) (m := 48147254661702201626) (k := 12) (by decide +kernel) c2039 c2050

def p2030 : Plan := .step 11 p2031 p2038
theorem c2030 : check p2030 48147254661702203674 12 = true := check_combine (v := 11) (l := p2031) (r := p2038) (m := 48147254661702203674) (k := 12) (by decide +kernel) c2031 c2038

def p2020 : Plan := .step 54 p2021 p2030
theorem c2020 : check p2020 48165269060211685658 12 = true := check_combine (v := 54) (l := p2021) (r := p2030) (m := 48165269060211685658) (k := 12) (by decide +kernel) c2021 c2030

def p2004 : Plan := .step 42 p2005 p2020
theorem c2004 : check p2004 48165273458258196762 12 = true := check_combine (v := 42) (l := p2005) (r := p2020) (m := 48165273458258196762) (k := 12) (by decide +kernel) c2005 c2020

def p2088 : Plan := .step 42 p2089 p2098
theorem c2088 : check p2088 47908577077138790418 12 = true := check_combine (v := 42) (l := p2089) (r := p2098) (m := 47908577077138790418) (k := 12) (by decide +kernel) c2089 c2098

def p2146 : Plan := .step 24 p2147 p2158
theorem c2146 : check p2146 647701984207907098 12 = true := check_combine (v := 24) (l := p2147) (r := p2158) (m := 647701984207907098) (k := 12) (by decide +kernel) c2147 c2158

def p2142 : Plan := .step 12 p2143 p2146
theorem c2142 : check p2142 647701984207911194 12 = true := check_combine (v := 12) (l := p2143) (r := p2146) (m := 647701984207911194) (k := 12) (by decide +kernel) c2143 c2146

def p2138 : Plan := .step 46 p2139 p2142
theorem c2138 : check p2138 647772352952088858 12 = true := check_combine (v := 46) (l := p2139) (r := p2142) (m := 647772352952088858) (k := 12) (by decide +kernel) c2139 c2142

def p2411 : Plan := .step 52 p2412 p2425
theorem c2411 : check p2411 48184357118324025370 13 = true := check_combine (v := 52) (l := p2412) (r := p2425) (m := 48184357118324025370) (k := 13) (by decide +kernel) c2412 c2425

def p2407 : Plan := .step 34 p2408 p2411
theorem c2407 : check p2407 48184357135503894554 13 = true := check_combine (v := 34) (l := p2408) (r := p2411) (m := 48184357135503894554) (k := 13) (by decide +kernel) c2408 c2411

def p2395 : Plan := .step 24 p2396 p2407
theorem c2395 : check p2395 48184357135520671770 13 = true := check_combine (v := 24) (l := p2396) (r := p2407) (m := 48184357135520671770) (k := 13) (by decide +kernel) c2396 c2407

def p2375 : Plan := .step 8 p2376 p2395
theorem c2375 : check p2375 48184357135520672026 13 = true := check_combine (v := 8) (l := p2376) (r := p2395) (m := 48184357135520672026) (k := 13) (by decide +kernel) c2376 c2395

def p2347 : Plan := .step 51 p2348 p2375
theorem c2347 : check p2347 48186608935334357274 13 = true := check_combine (v := 51) (l := p2348) (r := p2375) (m := 48186608935334357274) (k := 13) (by decide +kernel) c2348 c2375

def p2333 : Plan := .step 17 p2334 p2347
theorem c2333 : check p2333 48186608935334488346 13 = true := check_combine (v := 17) (l := p2334) (r := p2347) (m := 48186608935334488346) (k := 13) (by decide +kernel) c2334 c2347

def p2311 : Plan := .step 16 p2312 p2333
theorem c2311 : check p2311 48186608935334553882 13 = true := check_combine (v := 16) (l := p2312) (r := p2333) (m := 48186608935334553882) (k := 13) (by decide +kernel) c2312 c2333

def p2275 : Plan := .step 50 p2276 p2311
theorem c2275 : check p2275 48187734835241396506 13 = true := check_combine (v := 50) (l := p2276) (r := p2311) (m := 48187734835241396506) (k := 13) (by decide +kernel) c2276 c2311

def p2241 : Plan := .step 12 p2242 p2275
theorem c2241 : check p2241 48187734835241400602 13 = true := check_combine (v := 12) (l := p2242) (r := p2275) (m := 48187734835241400602) (k := 13) (by decide +kernel) c2242 c2275

def p2223 : Plan := .step 54 p2224 p2241
theorem c2223 : check p2223 48205749233750882586 13 = true := check_combine (v := 54) (l := p2224) (r := p2241) (m := 48205749233750882586) (k := 13) (by decide +kernel) c2224 c2241

def p2199 : Plan := .step 46 p2200 p2223
theorem c2199 : check p2199 48205819602495060250 13 = true := check_combine (v := 46) (l := p2200) (r := p2223) (m := 48205819602495060250) (k := 13) (by decide +kernel) c2200 c2223

def p2137 : Plan := .step 42 p2138 p2199
theorem c2137 : check p2137 48205824000541571354 13 = true := check_combine (v := 42) (l := p2138) (r := p2199) (m := 48205824000541571354) (k := 13) (by decide +kernel) c2138 c2199

def p2087 : Plan := .step 26 p2088 p2137
theorem c2087 : check p2087 48205824000608680218 13 = true := check_combine (v := 26) (l := p2088) (r := p2137) (m := 48205824000608680218) (k := 13) (by decide +kernel) c2088 c2137

def p2003 : Plan := .step 10 p2004 p2087
theorem c2003 : check p2003 48205824000608681242 13 = true := check_combine (v := 10) (l := p2004) (r := p2087) (m := 48205824000608681242) (k := 13) (by decide +kernel) c2004 c2087

def p1931 : Plan := .step 47 p1932 p2003
theorem c1931 : check p1931 48205964738097036570 13 = true := check_combine (v := 47) (l := p1932) (r := p2003) (m := 48205964738097036570) (k := 13) (by decide +kernel) c1932 c2003

def p1833 : Plan := .step 0 p1834 p1931
theorem c1833 : check p1833 48205964738097036571 13 = true := check_combine (v := 0) (l := p1834) (r := p1931) (m := 48205964738097036571) (k := 13) (by decide +kernel) c1834 c1931

def p1717 : Plan := .step 25 p1718 p1833
theorem c1717 : check p1717 48205964738130591003 13 = true := check_combine (v := 25) (l := p1718) (r := p1833) (m := 48205964738130591003) (k := 13) (by decide +kernel) c1718 c1833

def p1609 : Plan := .step 19 p1610 p1717
theorem c1609 : check p1609 48205964738131115291 13 = true := check_combine (v := 19) (l := p1610) (r := p1717) (m := 48205964738131115291) (k := 13) (by decide +kernel) c1610 c1717

def p1521 : Plan := .step 62 p1522 p1609
theorem c1521 : check p1521 52817650756558503195 13 = true := check_combine (v := 62) (l := p1522) (r := p1609) (m := 52817650756558503195) (k := 13) (by decide +kernel) c1522 c1609

def p1387 : Plan := .step 49 p1388 p1521
theorem c1387 : check p1387 52818213706511924507 13 = true := check_combine (v := 49) (l := p1388) (r := p1521) (m := 52818213706511924507) (k := 13) (by decide +kernel) c1388 c1521

def p1247 : Plan := .step 37 p1248 p1387
theorem c1247 : check p1247 52818213843950877979 13 = true := check_combine (v := 37) (l := p1248) (r := p1387) (m := 52818213843950877979) (k := 13) (by decide +kernel) c1248 c1387

def p1033 : Plan := .step 20 p1034 p1247
theorem c1033 : check p1033 52818213843951926555 13 = true := check_combine (v := 20) (l := p1034) (r := p1247) (m := 52818213843951926555) (k := 13) (by decide +kernel) c1034 c1247

def p839 : Plan := .step 9 p840 p1033
theorem c839 : check p839 52818213843951927067 13 = true := check_combine (v := 9) (l := p840) (r := p1033) (m := 52818213843951927067) (k := 13) (by decide +kernel) c840 c1033

def p611 : Plan := .step 7 p612 p839
theorem c611 : check p611 52818213843951927195 13 = true := check_combine (v := 7) (l := p612) (r := p839) (m := 52818213843951927195) (k := 13) (by decide +kernel) c612 c839

def p273 : Plan := .step 5 p274 p611
theorem c273 : check p273 52818213843951927227 13 = true := check_combine (v := 5) (l := p274) (r := p611) (m := 52818213843951927227) (k := 13) (by decide +kernel) c274 c611

def p1 : Plan := .step 23 p2 p273
theorem c1 : check p1 52818213843960315835 13 = true := check_combine (v := 23) (l := p2) (r := p273) (m := 52818213843960315835) (k := 13) (by decide +kernel) c2 c273

def p2626 : Plan := .step 44 p2627 p2640
theorem c2626 : check p2626 17744975443666824289 12 = true := check_combine (v := 44) (l := p2627) (r := p2640) (m := 17744975443666824289) (k := 12) (by decide +kernel) c2627 c2640

def p2612 : Plan := .step 15 p2613 p2626
theorem c2612 : check p2612 17744975443666857057 12 = true := check_combine (v := 15) (l := p2613) (r := p2626) (m := 17744975443666857057) (k := 12) (by decide +kernel) c2613 c2626

def p2596 : Plan := .step 64 p2597 p2612
theorem c2596 : check p2596 36191719517376408673 12 = true := check_combine (v := 64) (l := p2597) (r := p2612) (m := 36191719517376408673) (k := 12) (by decide +kernel) c2597 c2612

def p2584 : Plan := .step 50 p2585 p2596
theorem c2584 : check p2584 36192845417283251297 12 = true := check_combine (v := 50) (l := p2585) (r := p2596) (m := 36192845417283251297) (k := 12) (by decide +kernel) c2585 c2596

def p2566 : Plan := .step 42 p2567 p2584
theorem c2566 : check p2566 36192849815329762401 12 = true := check_combine (v := 42) (l := p2567) (r := p2584) (m := 36192849815329762401) (k := 12) (by decide +kernel) c2567 c2584

def p2552 : Plan := .step 39 p2553 p2566
theorem c2552 : check p2552 36192850365085576289 12 = true := check_combine (v := 39) (l := p2553) (r := p2566) (m := 36192850365085576289) (k := 12) (by decide +kernel) c2553 c2566

def p2530 : Plan := .step 36 p2531 p2552
theorem c2530 : check p2530 36192850433805053025 12 = true := check_combine (v := 36) (l := p2531) (r := p2552) (m := 36192850433805053025) (k := 12) (by decide +kernel) c2531 c2552

def p2506 : Plan := .step 16 p2507 p2530
theorem c2506 : check p2506 36192850433805118561 12 = true := check_combine (v := 16) (l := p2507) (r := p2530) (m := 36192850433805118561) (k := 12) (by decide +kernel) c2507 c2530

def p2462 : Plan := .step 8 p2463 p2506
theorem c2462 : check p2462 36192850433805118817 12 = true := check_combine (v := 8) (l := p2463) (r := p2506) (m := 36192850433805118817) (k := 12) (by decide +kernel) c2463 c2506

def p2856 : Plan := .step 40 p2857 p2872
theorem c2856 : check p2856 7810346853779828080 12 = true := check_combine (v := 40) (l := p2857) (r := p2872) (m := 7810346853779828080) (k := 12) (by decide +kernel) c2857 c2872

def p2846 : Plan := .step 25 p2847 p2856
theorem c2846 : check p2846 7810346853813382512 12 = true := check_combine (v := 25) (l := p2847) (r := p2856) (m := 7810346853813382512) (k := 12) (by decide +kernel) c2847 c2856

def p2832 : Plan := .step 19 p2833 p2846
theorem c2832 : check p2832 7810346853813906800 12 = true := check_combine (v := 19) (l := p2833) (r := p2846) (m := 7810346853813906800) (k := 12) (by decide +kernel) c2833 c2846

def p2816 : Plan := .step 64 p2817 p2832
theorem c2816 : check p2816 26257090927523458416 12 = true := check_combine (v := 64) (l := p2817) (r := p2832) (m := 26257090927523458416) (k := 12) (by decide +kernel) c2817 c2832

def p2802 : Plan := .step 63 p2803 p2816
theorem c2802 : check p2802 35480462964378234224 12 = true := check_combine (v := 63) (l := p2803) (r := p2816) (m := 35480462964378234224) (k := 12) (by decide +kernel) c2803 c2816

def p2784 : Plan := .step 39 p2785 p2802
theorem c2784 : check p2784 35480463514134048112 12 = true := check_combine (v := 39) (l := p2785) (r := p2802) (m := 35480463514134048112) (k := 12) (by decide +kernel) c2785 c2802

def p2756 : Plan := .step 18 p2757 p2784
theorem c2756 : check p2756 35480463514134310256 12 = true := check_combine (v := 18) (l := p2757) (r := p2784) (m := 35480463514134310256) (k := 12) (by decide +kernel) c2757 c2784

def p2716 : Plan := .step 60 p2717 p2756
theorem c2716 : check p2716 36633385018741157232 12 = true := check_combine (v := 60) (l := p2717) (r := p2756) (m := 36633385018741157232) (k := 12) (by decide +kernel) c2717 c2756

def p2678 : Plan := .step 50 p2679 p2716
theorem c2678 : check p2678 36634510918647999856 12 = true := check_combine (v := 50) (l := p2679) (r := p2716) (m := 36634510918647999856) (k := 12) (by decide +kernel) c2679 c2716

def p2994 : Plan := .step 44 p2995 p3014
theorem c2994 : check p2994 7395035001197063200 12 = true := check_combine (v := 44) (l := p2995) (r := p3014) (m := 7395035001197063200) (k := 12) (by decide +kernel) c2995 c3014

def p2988 : Plan := .step 48 p2989 p2994
theorem c2988 : check p2988 7395316476173773856 12 = true := check_combine (v := 48) (l := p2989) (r := p2994) (m := 7395316476173773856) (k := 12) (by decide +kernel) c2989 c2994

def p2972 : Plan := .step 15 p2973 p2988
theorem c2972 : check p2972 7395316476173806624 12 = true := check_combine (v := 15) (l := p2973) (r := p2988) (m := 7395316476173806624) (k := 12) (by decide +kernel) c2973 c2988

def p2960 : Plan := .step 36 p2961 p2972
theorem c2960 : check p2960 7395316544893283360 12 = true := check_combine (v := 36) (l := p2961) (r := p2972) (m := 7395316544893283360) (k := 12) (by decide +kernel) c2961 c2972

def p2952 : Plan := .step 64 p2953 p2960
theorem c2952 : check p2952 25842060618602834976 12 = true := check_combine (v := 64) (l := p2953) (r := p2960) (m := 25842060618602834976) (k := 12) (by decide +kernel) c2953 c2960

def p2940 : Plan := .step 39 p2941 p2952
theorem c2940 : check p2940 25842061168358648864 12 = true := check_combine (v := 39) (l := p2941) (r := p2952) (m := 25842061168358648864) (k := 12) (by decide +kernel) c2941 c2952

def p2922 : Plan := .step 8 p2923 p2940
theorem c2922 : check p2922 25842061168358649120 12 = true := check_combine (v := 8) (l := p2923) (r := p2940) (m := 25842061168358649120) (k := 12) (by decide +kernel) c2923 c2940

def p2908 : Plan := .step 60 p2909 p2922
theorem c2908 : check p2908 26994982672965496096 12 = true := check_combine (v := 60) (l := p2909) (r := p2922) (m := 26994982672965496096) (k := 12) (by decide +kernel) c2909 c2922

def p3190 : Plan := .step 46 p3191 p3196
theorem c3190 : check p3190 27427741642799474769 12 = true := check_combine (v := 46) (l := p3191) (r := p3196) (m := 27427741642799474769) (k := 12) (by decide +kernel) c3191 c3196

def p3180 : Plan := .step 21 p3181 p3190
theorem c3180 : check p3180 27427741642801571921 12 = true := check_combine (v := 21) (l := p3181) (r := p3190) (m := 27427741642801571921) (k := 12) (by decide +kernel) c3181 c3190

def p3170 : Plan := .step 5 p3171 p3180
theorem c3170 : check p3170 27427741642801571953 12 = true := check_combine (v := 5) (l := p3171) (r := p3180) (m := 27427741642801571953) (k := 12) (by decide +kernel) c3171 c3180

def p3156 : Plan := .step 50 p3157 p3170
theorem c3156 : check p3156 27428867542708414577 12 = true := check_combine (v := 50) (l := p3157) (r := p3170) (m := 27428867542708414577) (k := 12) (by decide +kernel) c3157 c3170

def p3142 : Plan := .step 48 p3143 p3156
theorem c3142 : check p3142 27429149017685125233 12 = true := check_combine (v := 48) (l := p3143) (r := p3156) (m := 27429149017685125233) (k := 12) (by decide +kernel) c3143 c3156

def p3116 : Plan := .step 18 p3117 p3142
theorem c3116 : check p3116 27429149017685387377 12 = true := check_combine (v := 18) (l := p3117) (r := p3142) (m := 27429149017685387377) (k := 12) (by decide +kernel) c3117 c3142

def p3082 : Plan := .step 10 p3083 p3116
theorem c3082 : check p3082 27429149017685388401 12 = true := check_combine (v := 10) (l := p3083) (r := p3116) (m := 27429149017685388401) (k := 12) (by decide +kernel) c3083 c3116

def p3052 : Plan := .step 19 p3053 p3082
theorem c3052 : check p3052 27429149017685912689 12 = true := check_combine (v := 19) (l := p3053) (r := p3082) (m := 27429149017685912689) (k := 12) (by decide +kernel) c3053 c3082

def p3302 : Plan := .step 32 p3303 p3308
theorem c3302 : check p3302 4803041891826429025 12 = true := check_combine (v := 32) (l := p3303) (r := p3308) (m := 4803041891826429025) (k := 12) (by decide +kernel) c3303 c3308

def p3290 : Plan := .step 36 p3291 p3302
theorem c3290 : check p3290 4803041960545905761 12 = true := check_combine (v := 36) (l := p3291) (r := p3302) (m := 4803041960545905761) (k := 12) (by decide +kernel) c3291 c3302

def p3276 : Plan := .step 8 p3277 p3290
theorem c3276 : check p3276 4803041960545906017 12 = true := check_combine (v := 8) (l := p3277) (r := p3290) (m := 4803041960545906017) (k := 12) (by decide +kernel) c3277 c3290

def p3268 : Plan := .step 64 p3269 p3276
theorem c3268 : check p3268 23249786034255457633 12 = true := check_combine (v := 64) (l := p3269) (r := p3276) (m := 23249786034255457633) (k := 12) (by decide +kernel) c3269 c3276

def p3256 : Plan := .step 39 p3257 p3268
theorem c3256 : check p3256 23249786584011271521 12 = true := check_combine (v := 39) (l := p3257) (r := p3268) (m := 23249786584011271521) (k := 12) (by decide +kernel) c3257 c3268

def p3240 : Plan := .step 18 p3241 p3256
theorem c3240 : check p3240 23249786584011533665 12 = true := check_combine (v := 18) (l := p3241) (r := p3256) (m := 23249786584011533665) (k := 12) (by decide +kernel) c3241 c3256

def p3406 : Plan := .step 27 p3407 p3414
theorem c3406 : check p3406 22365624206255746400 12 = true := check_combine (v := 27) (l := p3407) (r := p3414) (m := 22365624206255746400) (k := 12) (by decide +kernel) c3407 c3414

def p3398 : Plan := .step 0 p3399 p3406
theorem c3398 : check p3398 22365624206255746401 12 = true := check_combine (v := 0) (l := p3399) (r := p3406) (m := 22365624206255746401) (k := 12) (by decide +kernel) c3399 c3406

def p3384 : Plan := .step 40 p3385 p3398
theorem c3384 : check p3384 22365625305767374177 12 = true := check_combine (v := 40) (l := p3385) (r := p3398) (m := 22365625305767374177) (k := 12) (by decide +kernel) c3385 c3398

def p3370 : Plan := .step 25 p3371 p3384
theorem c3370 : check p3370 22365625305800928609 12 = true := check_combine (v := 25) (l := p3371) (r := p3384) (m := 22365625305800928609) (k := 12) (by decide +kernel) c3371 c3384

def p3356 : Plan := .step 17 p3357 p3370
theorem c3356 : check p3356 22365625305801059681 12 = true := check_combine (v := 17) (l := p3357) (r := p3370) (m := 22365625305801059681) (k := 12) (by decide +kernel) c3357 c3370

def p3524 : Plan := .step 40 p3525 p3536
theorem c3524 : check p3524 22979141173468619889 12 = true := check_combine (v := 40) (l := p3525) (r := p3536) (m := 22979141173468619889) (k := 12) (by decide +kernel) c3525 c3536

def p3510 : Plan := .step 24 p3511 p3524
theorem c3510 : check p3510 22979141173485397105 12 = true := check_combine (v := 24) (l := p3511) (r := p3524) (m := 22979141173485397105) (k := 12) (by decide +kernel) c3511 c3524

def p3498 : Plan := .step 32 p3499 p3510
theorem c3498 : check p3498 22979141177780364401 12 = true := check_combine (v := 32) (l := p3499) (r := p3510) (m := 22979141177780364401) (k := 12) (by decide +kernel) c3499 c3510

def p3480 : Plan := .step 29 p3481 p3498
theorem c3480 : check p3480 22979141178317235313 12 = true := check_combine (v := 29) (l := p3481) (r := p3498) (m := 22979141178317235313) (k := 12) (by decide +kernel) c3481 c3498

def p3458 : Plan := .step 22 p3459 p3480
theorem c3458 : check p3458 22979141178321429617 12 = true := check_combine (v := 22) (l := p3459) (r := p3480) (m := 22979141178321429617) (k := 12) (by decide +kernel) c3459 c3480

def p3652 : Plan := .step 32 p3653 p3666
theorem c3652 : check p3652 1074089411567840305 12 = true := check_combine (v := 32) (l := p3653) (r := p3666) (m := 1074089411567840305) (k := 12) (by decide +kernel) c3653 c3666

def p3646 : Plan := .step 29 p3647 p3652
theorem c3646 : check p3646 1074089412104711217 12 = true := check_combine (v := 29) (l := p3647) (r := p3652) (m := 1074089412104711217) (k := 12) (by decide +kernel) c3647 c3652

def p3634 : Plan := .step 22 p3635 p3646
theorem c3634 : check p3634 1074089412108905521 12 = true := check_combine (v := 22) (l := p3635) (r := p3646) (m := 1074089412108905521) (k := 12) (by decide +kernel) c3635 c3646

def p3602 : Plan := .step 18 p3603 p3634
theorem c3602 : check p3602 1074089412109167665 12 = true := check_combine (v := 18) (l := p3603) (r := p3634) (m := 1074089412109167665) (k := 12) (by decide +kernel) c3603 c3634

def p3582 : Plan := .step 60 p3583 p3602
theorem c3582 : check p3582 2227010916716014641 12 = true := check_combine (v := 60) (l := p3583) (r := p3602) (m := 2227010916716014641) (k := 12) (by decide +kernel) c3583 c3602

def p3738 : Plan := .step 0 p3739 p3750
theorem c3738 : check p3738 21781371691779630449 12 = true := check_combine (v := 0) (l := p3739) (r := p3750) (m := 21781371691779630449) (k := 12) (by decide +kernel) c3739 c3750

def p3714 : Plan := .step 39 p3715 p3738
theorem c3714 : check p3714 21781372241535444337 12 = true := check_combine (v := 39) (l := p3715) (r := p3738) (m := 21781372241535444337) (k := 12) (by decide +kernel) c3715 c3738

def p3834 : Plan := .step 37 p3835 p3846
theorem c3834 : check p3834 3343903082582010224 12 = true := check_combine (v := 37) (l := p3835) (r := p3846) (m := 3343903082582010224) (k := 12) (by decide +kernel) c3835 c3846

def p3828 : Plan := .step 34 p3829 p3834
theorem c3828 : check p3828 3343903099761879408 12 = true := check_combine (v := 34) (l := p3829) (r := p3834) (m := 3343903099761879408) (k := 12) (by decide +kernel) c3829 c3834

def p3816 : Plan := .step 24 p3817 p3828
theorem c3816 : check p3816 3343903099778656624 12 = true := check_combine (v := 24) (l := p3817) (r := p3828) (m := 3343903099778656624) (k := 12) (by decide +kernel) c3817 c3828

def p3794 : Plan := .step 18 p3795 p3816
theorem c3794 : check p3794 3343903099778918768 12 = true := check_combine (v := 18) (l := p3795) (r := p3816) (m := 3343903099778918768) (k := 12) (by decide +kernel) c3795 c3816

def p3932 : Plan := .step 22 p3933 p3944
theorem c3932 : check p3932 21807975479422099728 12 = true := check_combine (v := 22) (l := p3933) (r := p3944) (m := 21807975479422099728) (k := 12) (by decide +kernel) c3933 c3944

def p3908 : Plan := .step 39 p3909 p3932
theorem c3908 : check p3908 21807976029177913616 12 = true := check_combine (v := 39) (l := p3909) (r := p3932) (m := 21807976029177913616) (k := 12) (by decide +kernel) c3909 c3932

def p3894 : Plan := .step 5 p3895 p3908
theorem c3894 : check p3894 21807976029177913648 12 = true := check_combine (v := 5) (l := p3895) (r := p3908) (m := 21807976029177913648) (k := 12) (by decide +kernel) c3895 c3908

def p3998 : Plan := .step 39 p3999 p4018
theorem c3998 : check p3998 19231459641185673553 12 = true := check_combine (v := 39) (l := p3999) (r := p4018) (m := 19231459641185673553) (k := 12) (by decide +kernel) c3999 c4018

def p3986 : Plan := .step 5 p3987 p3998
theorem c3986 : check p3986 19231459641185673585 12 = true := check_combine (v := 5) (l := p3987) (r := p3998) (m := 19231459641185673585) (k := 12) (by decide +kernel) c3987 c3998

def p4208 : Plan := .step 29 p4209 p4216
theorem c4208 : check p4208 21789468954822977616 12 = true := check_combine (v := 29) (l := p4209) (r := p4216) (m := 21789468954822977616) (k := 12) (by decide +kernel) c4209 c4216

def p4198 : Plan := .step 33 p4199 p4208
theorem c4198 : check p4198 21789468963412912208 12 = true := check_combine (v := 33) (l := p4199) (r := p4208) (m := 21789468963412912208) (k := 12) (by decide +kernel) c4199 c4208

def p4363 : Plan := .step 42 p4364 p4389
theorem c4363 : check p4363 3378824179622111313 13 = true := check_combine (v := 42) (l := p4364) (r := p4389) (m := 3378824179622111313) (k := 13) (by decide +kernel) c4364 c4389

def p4333 : Plan := .step 32 p4334 p4363
theorem c4333 : check p4333 3378824183917078609 13 = true := check_combine (v := 32) (l := p4334) (r := p4363) (m := 3378824183917078609) (k := 13) (by decide +kernel) c4334 c4363

def p4305 : Plan := .step 29 p4306 p4333
theorem c4305 : check p4305 3378824184453949521 13 = true := check_combine (v := 29) (l := p4306) (r := p4333) (m := 3378824184453949521) (k := 13) (by decide +kernel) c4306 c4333

def p4293 : Plan := .step 64 p4294 p4305
theorem c4293 : check p4293 21825568258163501137 13 = true := check_combine (v := 64) (l := p4294) (r := p4305) (m := 21825568258163501137) (k := 13) (by decide +kernel) c4294 c4305

def p4263 : Plan := .step 33 p4264 p4293
theorem c4263 : check p4263 21825568266753435729 13 = true := check_combine (v := 33) (l := p4264) (r := p4293) (m := 21825568266753435729) (k := 13) (by decide +kernel) c4264 c4293

def p4197 : Plan := .step 8 p4198 p4263
theorem c4197 : check p4197 21825568266753435985 13 = true := check_combine (v := 8) (l := p4198) (r := p4263) (m := 21825568266753435985) (k := 13) (by decide +kernel) c4198 c4263

def p4151 : Plan := .step 34 p4152 p4197
theorem c4151 : check p4151 21825568283933305169 13 = true := check_combine (v := 34) (l := p4152) (r := p4197) (m := 21825568283933305169) (k := 13) (by decide +kernel) c4152 c4197

def p4115 : Plan := .step 24 p4116 p4151
theorem c4115 : check p4115 21825568283950082385 13 = true := check_combine (v := 24) (l := p4116) (r := p4151) (m := 21825568283950082385) (k := 13) (by decide +kernel) c4116 c4151

def p4087 : Plan := .step 17 p4088 p4115
theorem c4087 : check p4087 21825568283950213457 13 = true := check_combine (v := 17) (l := p4088) (r := p4115) (m := 21825568283950213457) (k := 13) (by decide +kernel) c4088 c4115

def p4051 : Plan := .step 5 p4052 p4087
theorem c4051 : check p4051 21825568283950213489 13 = true := check_combine (v := 5) (l := p4052) (r := p4087) (m := 21825568283950213489) (k := 13) (by decide +kernel) c4052 c4087

def p3985 : Plan := .step 50 p3986 p4051
theorem c3985 : check p3985 21826694183857056113 13 = true := check_combine (v := 50) (l := p3986) (r := p4051) (m := 21826694183857056113) (k := 13) (by decide +kernel) c3986 c4051

def p3893 : Plan := .step 18 p3894 p3985
theorem c3893 : check p3893 21826694183857318257 13 = true := check_combine (v := 18) (l := p3894) (r := p3985) (m := 21826694183857318257) (k := 13) (by decide +kernel) c3894 c3985

def p3793 : Plan := .step 10 p3794 p3893
theorem c3793 : check p3793 21826694183857319281 13 = true := check_combine (v := 10) (l := p3794) (r := p3893) (m := 21826694183857319281) (k := 13) (by decide +kernel) c3794 c3893

def p3713 : Plan := .step 60 p3714 p3793
theorem c3713 : check p3713 22979615688464166257 13 = true := check_combine (v := 60) (l := p3714) (r := p3793) (m := 22979615688464166257) (k := 13) (by decide +kernel) c3714 c3793

def p3581 : Plan := .step 40 p3582 p3713
theorem c3581 : check p3581 22979616787975794033 13 = true := check_combine (v := 40) (l := p3582) (r := p3713) (m := 22979616787975794033) (k := 13) (by decide +kernel) c3582 c3713

def p3457 : Plan := .step 25 p3458 p3581
theorem c3457 : check p3457 22979616788009348465 13 = true := check_combine (v := 25) (l := p3458) (r := p3581) (m := 22979616788009348465) (k := 13) (by decide +kernel) c3458 c3581

def p3355 : Plan := .step 62 p3356 p3457
theorem c3355 : check p3355 27591302806436736369 13 = true := check_combine (v := 62) (l := p3356) (r := p3457) (m := 27591302806436736369) (k := 13) (by decide +kernel) c3356 c3457

def p3239 : Plan := .step 19 p3240 p3355
theorem c3239 : check p3239 27591302806437260657 13 = true := check_combine (v := 19) (l := p3240) (r := p3355) (m := 27591302806437260657) (k := 13) (by decide +kernel) c3240 c3355

def p3051 : Plan := .step 15 p3052 p3239
theorem c3051 : check p3051 27591302806437293425 13 = true := check_combine (v := 15) (l := p3052) (r := p3239) (m := 27591302806437293425) (k := 13) (by decide +kernel) c3052 c3239

def p2907 : Plan := .step 63 p2908 p3051
theorem c2907 : check p2907 36814674843292069233 13 = true := check_combine (v := 63) (l := p2908) (r := p3051) (m := 36814674843292069233) (k := 13) (by decide +kernel) c2908 c3051

def p2677 : Plan := .step 16 p2678 p2907
theorem c2677 : check p2677 36814674843292134769 13 = true := check_combine (v := 16) (l := p2678) (r := p2907) (m := 36814674843292134769) (k := 13) (by decide +kernel) c2678 c2907

def p2461 : Plan := .step 7 p2462 p2677
theorem c2461 : check p2461 36814674843292134897 13 = true := check_combine (v := 7) (l := p2462) (r := p2677) (m := 36814674843292134897) (k := 13) (by decide +kernel) c2462 c2677

def p4514 : Plan := .step 40 p4515 p4522
theorem c4514 : check p4514 58258367989199326560 12 = true := check_combine (v := 40) (l := p4515) (r := p4522) (m := 58258367989199326560) (k := 12) (by decide +kernel) c4515 c4522

def p4504 : Plan := .step 60 p4505 p4514
theorem c4504 : check p4504 59411289493806173536 12 = true := check_combine (v := 60) (l := p4505) (r := p4514) (m := 59411289493806173536) (k := 12) (by decide +kernel) c4505 c4514

def p4492 : Plan := .step 45 p4493 p4504
theorem c4492 : check p4492 59411324678178262368 12 = true := check_combine (v := 45) (l := p4493) (r := p4504) (m := 59411324678178262368) (k := 12) (by decide +kernel) c4493 c4504

def p4482 : Plan := .step 58 p4483 p4492
theorem c4482 : check p4482 59699555054329974112 12 = true := check_combine (v := 58) (l := p4483) (r := p4492) (m := 59699555054329974112) (k := 12) (by decide +kernel) c4483 c4492

def p4470 : Plan := .step 47 p4471 p4482
theorem c4470 : check p4470 59699695791818329440 12 = true := check_combine (v := 47) (l := p4471) (r := p4482) (m := 59699695791818329440) (k := 12) (by decide +kernel) c4471 c4482

def p4456 : Plan := .step 39 p4457 p4470
theorem c4456 : check p4456 59699696341574143328 12 = true := check_combine (v := 39) (l := p4457) (r := p4470) (m := 59699696341574143328) (k := 12) (by decide +kernel) c4457 c4470

def p4428 : Plan := .step 36 p4429 p4456
theorem c4428 : check p4428 59699696410293620064 12 = true := check_combine (v := 36) (l := p4429) (r := p4456) (m := 59699696410293620064) (k := 12) (by decide +kernel) c4429 c4456

def p4714 : Plan := .step 61 p4715 p4726
theorem c4714 : check p4714 58257789175977082912 12 = true := check_combine (v := 61) (l := p4715) (r := p4726) (m := 58257789175977082912) (k := 12) (by decide +kernel) c4715 c4726

def p4692 : Plan := .step 11 p4693 p4714
theorem c4692 : check p4692 58257789175977084960 12 = true := check_combine (v := 11) (l := p4693) (r := p4714) (m := 58257789175977084960) (k := 12) (by decide +kernel) c4693 c4714

def p4672 : Plan := .step 49 p4673 p4692
theorem c4672 : check p4672 58258352125930506272 12 = true := check_combine (v := 49) (l := p4673) (r := p4692) (m := 58258352125930506272) (k := 12) (by decide +kernel) c4673 c4692

def p4658 : Plan := .step 10 p4659 p4672
theorem c4658 : check p4658 58258352125930507296 12 = true := check_combine (v := 10) (l := p4659) (r := p4672) (m := 58258352125930507296) (k := 12) (by decide +kernel) c4659 c4672

def p4634 : Plan := .step 6 p4635 p4658
theorem c4634 : check p4634 58258352125930507360 12 = true := check_combine (v := 6) (l := p4635) (r := p4658) (m := 58258352125930507360) (k := 12) (by decide +kernel) c4635 c4658

def p4618 : Plan := .step 60 p4619 p4634
theorem c4618 : check p4618 59411273630537354336 12 = true := check_combine (v := 60) (l := p4619) (r := p4634) (m := 59411273630537354336) (k := 12) (by decide +kernel) c4619 c4634

def p4594 : Plan := .step 58 p4595 p4618
theorem c4594 : check p4594 59699504006689066080 12 = true := check_combine (v := 58) (l := p4595) (r := p4618) (m := 59699504006689066080) (k := 12) (by decide +kernel) c4595 c4618

def p4564 : Plan := .step 47 p4565 p4594
theorem c4564 : check p4564 59699644744177421408 12 = true := check_combine (v := 47) (l := p4565) (r := p4594) (m := 59699644744177421408) (k := 12) (by decide +kernel) c4565 c4594

def p4868 : Plan := .step 23 p4869 p4878
theorem c4868 : check p4868 41248164585837611104 12 = true := check_combine (v := 23) (l := p4869) (r := p4878) (m := 41248164585837611104) (k := 12) (by decide +kernel) c4869 c4878

def p4854 : Plan := .step 48 p4855 p4868
theorem c4854 : check p4854 41248446060814321760 12 = true := check_combine (v := 48) (l := p4855) (r := p4868) (m := 41248446060814321760) (k := 12) (by decide +kernel) c4855 c4868

def p4826 : Plan := .step 42 p4827 p4854
theorem c4826 : check p4826 41248450458860832864 12 = true := check_combine (v := 42) (l := p4827) (r := p4854) (m := 41248450458860832864) (k := 12) (by decide +kernel) c4827 c4854

def p4810 : Plan := .step 18 p4811 p4826
theorem c4810 : check p4810 41248450458861095008 12 = true := check_combine (v := 18) (l := p4811) (r := p4826) (m := 41248450458861095008) (k := 12) (by decide +kernel) c4811 c4826

def p4770 : Plan := .step 32 p4771 p4810
theorem c4770 : check p4770 41248450463156062304 12 = true := check_combine (v := 32) (l := p4771) (r := p4810) (m := 41248450463156062304) (k := 12) (by decide +kernel) c4771 c4810

def p5020 : Plan := .step 14 p5021 p5034
theorem c5020 : check p5020 1754010908240265281 12 = true := check_combine (v := 14) (l := p5021) (r := p5034) (m := 1754010908240265281) (k := 12) (by decide +kernel) c5021 c5034

def p5002 : Plan := .step 11 p5003 p5020
theorem c5002 : check p5002 1754010908240267329 12 = true := check_combine (v := 11) (l := p5003) (r := p5020) (m := 1754010908240267329) (k := 12) (by decide +kernel) c5003 c5020

def p4978 : Plan := .step 5 p4979 p5002
theorem c4978 : check p4978 1754010908240267361 12 = true := check_combine (v := 5) (l := p4979) (r := p5002) (m := 1754010908240267361) (k := 12) (by decide +kernel) c4979 c5002

def p4964 : Plan := .step 36 p4965 p4978
theorem c4964 : check p4964 1754010976959744097 12 = true := check_combine (v := 36) (l := p4965) (r := p4978) (m := 1754010976959744097) (k := 12) (by decide +kernel) c4965 c4978

def p4950 : Plan := .step 15 p4951 p4964
theorem c4950 : check p4950 1754010976959776865 12 = true := check_combine (v := 15) (l := p4951) (r := p4964) (m := 1754010976959776865) (k := 12) (by decide +kernel) c4951 c4964

def p4936 : Plan := .step 61 p4937 p4950
theorem c4936 : check p4936 4059853986173470817 12 = true := check_combine (v := 61) (l := p4937) (r := p4950) (m := 4059853986173470817) (k := 12) (by decide +kernel) c4937 c4950

def p4924 : Plan := .step 58 p4925 p4936
theorem c4924 : check p4924 4348084362325182561 12 = true := check_combine (v := 58) (l := p4925) (r := p4936) (m := 4348084362325182561) (k := 12) (by decide +kernel) c4925 c4936

def p5120 : Plan := .step 27 p5121 p5132
theorem c5120 : check p5120 19346723712340609121 12 = true := check_combine (v := 27) (l := p5121) (r := p5132) (m := 19346723712340609121) (k := 12) (by decide +kernel) c5121 c5132

def p5112 : Plan := .step 15 p5113 p5120
theorem c5112 : check p5112 19346723712340641889 12 = true := check_combine (v := 15) (l := p5113) (r := p5120) (m := 19346723712340641889) (k := 12) (by decide +kernel) c5113 c5120

def p5102 : Plan := .step 25 p5103 p5112
theorem c5102 : check p5102 19346723712374196321 12 = true := check_combine (v := 25) (l := p5103) (r := p5112) (m := 19346723712374196321) (k := 12) (by decide +kernel) c5103 c5112

def p5092 : Plan := .step 60 p5093 p5102
theorem c5092 : check p5092 20499645216981043297 12 = true := check_combine (v := 60) (l := p5093) (r := p5102) (m := 20499645216981043297) (k := 12) (by decide +kernel) c5093 c5102

def p5082 : Plan := .step 40 p5083 p5092
theorem c5082 : check p5082 20499646316492671073 12 = true := check_combine (v := 40) (l := p5083) (r := p5092) (m := 20499646316492671073) (k := 12) (by decide +kernel) c5083 c5092

def p5192 : Plan := .step 23 p5193 p5200
theorem c5192 : check p5192 59443147509917337632 12 = true := check_combine (v := 23) (l := p5193) (r := p5200) (m := 59443147509917337632) (k := 12) (by decide +kernel) c5193 c5200

def p5180 : Plan := .step 6 p5181 p5192
theorem c5180 : check p5180 59443147509917337696 12 = true := check_combine (v := 6) (l := p5181) (r := p5192) (m := 59443147509917337696) (k := 12) (by decide +kernel) c5181 c5192

def p5248 : Plan := .step 39 p5249 p5254
theorem c5248 : check p5248 58246315836794372193 12 = true := check_combine (v := 39) (l := p5249) (r := p5254) (m := 58246315836794372193) (k := 12) (by decide +kernel) c5249 c5254

def p5324 : Plan := .step 43 p5325 p5332
theorem c5324 : check p5324 21353076797438314529 12 = true := check_combine (v := 43) (l := p5325) (r := p5332) (m := 21353076797438314529) (k := 12) (by decide +kernel) c5325 c5332

def p5312 : Plan := .step 25 p5313 p5324
theorem c5312 : check p5312 21353076797471868961 12 = true := check_combine (v := 25) (l := p5313) (r := p5324) (m := 21353076797471868961) (k := 12) (by decide +kernel) c5313 c5324

def p5298 : Plan := .step 15 p5299 p5312
theorem c5298 : check p5298 21353076797471901729 12 = true := check_combine (v := 15) (l := p5299) (r := p5312) (m := 21353076797471901729) (k := 12) (by decide +kernel) c5299 c5312

def p5646 : Plan := .step 33 p5647 p5660
theorem c5646 : check p5646 58274677743289368608 12 = true := check_combine (v := 33) (l := p5647) (r := p5660) (m := 58274677743289368608) (k := 12) (by decide +kernel) c5647 c5660

def p5642 : Plan := .step 26 p5643 p5646
theorem c5642 : check p5642 58274677743356477472 12 = true := check_combine (v := 26) (l := p5643) (r := p5646) (m := 58274677743356477472) (k := 12) (by decide +kernel) c5643 c5646

def p5636 : Plan := .step 22 p5637 p5642
theorem c5636 : check p5636 58274677743360671776 12 = true := check_combine (v := 22) (l := p5637) (r := p5642) (m := 58274677743360671776) (k := 12) (by decide +kernel) c5637 c5642

def p5755 : Plan := .step 11 p5756 p5773
theorem c5755 : check p5755 55968834785628932097 13 = true := check_combine (v := 11) (l := p5756) (r := p5773) (m := 55968834785628932097) (k := 13) (by decide +kernel) c5756 c5773

def p5751 : Plan := .step 54 p5752 p5755
theorem c5751 : check p5751 55986849184138414081 13 = true := check_combine (v := 54) (l := p5752) (r := p5755) (m := 55986849184138414081) (k := 13) (by decide +kernel) c5752 c5755

def p5741 : Plan := .step 26 p5742 p5751
theorem c5741 : check p5741 55986849184205522945 13 = true := check_combine (v := 26) (l := p5742) (r := p5751) (m := 55986849184205522945) (k := 13) (by decide +kernel) c5742 c5751

def p5731 : Plan := .step 5 p5732 p5741
theorem c5731 : check p5731 55986849184205522977 13 = true := check_combine (v := 5) (l := p5732) (r := p5741) (m := 55986849184205522977) (k := 13) (by decide +kernel) c5732 c5741

def p5717 : Plan := .step 61 p5718 p5731
theorem c5717 : check p5717 58292692193419216929 13 = true := check_combine (v := 61) (l := p5718) (r := p5731) (m := 58292692193419216929) (k := 13) (by decide +kernel) c5718 c5731

def p5695 : Plan := .step 34 p5696 p5717
theorem c5695 : check p5695 58292692210599086113 13 = true := check_combine (v := 34) (l := p5696) (r := p5717) (m := 58292692210599086113) (k := 13) (by decide +kernel) c5696 c5717

def p5635 : Plan := .step 18 p5636 p5695
theorem c5635 : check p5635 58292692210599348257 13 = true := check_combine (v := 18) (l := p5636) (r := p5695) (m := 58292692210599348257) (k := 13) (by decide +kernel) c5636 c5695

def p5603 : Plan := .step 17 p5604 p5635
theorem c5603 : check p5603 58292692210599479329 13 = true := check_combine (v := 17) (l := p5604) (r := p5635) (m := 58292692210599479329) (k := 13) (by decide +kernel) c5604 c5635

def p5571 : Plan := .step 27 p5572 p5603
theorem c5571 : check p5571 58292692210733697057 13 = true := check_combine (v := 27) (l := p5572) (r := p5603) (m := 58292692210733697057) (k := 13) (by decide +kernel) c5572 c5603

def p5545 : Plan := .step 50 p5546 p5571
theorem c5545 : check p5545 58293818110640539681 13 = true := check_combine (v := 50) (l := p5546) (r := p5571) (m := 58293818110640539681) (k := 13) (by decide +kernel) c5546 c5571

def p5507 : Plan := .step 40 p5508 p5545
theorem c5507 : check p5507 58293819210152167457 13 = true := check_combine (v := 40) (l := p5508) (r := p5545) (m := 58293819210152167457) (k := 13) (by decide +kernel) c5508 c5545

def p5463 : Plan := .step 25 p5464 p5507
theorem c5463 : check p5463 58293819210185721889 13 = true := check_combine (v := 25) (l := p5464) (r := p5507) (m := 58293819210185721889) (k := 13) (by decide +kernel) c5464 c5507

def p5425 : Plan := .step 46 p5426 p5463
theorem c5425 : check p5425 58293889578929899553 13 = true := check_combine (v := 46) (l := p5426) (r := p5463) (m := 58293889578929899553) (k := 13) (by decide +kernel) c5426 c5463

def p5379 : Plan := .step 15 p5380 p5425
theorem c5379 : check p5379 58293889578929932321 13 = true := check_combine (v := 15) (l := p5380) (r := p5425) (m := 58293889578929932321) (k := 13) (by decide +kernel) c5380 c5425

def p5297 : Plan := .step 6 p5298 p5379
theorem c5297 : check p5297 58293889578929932385 13 = true := check_combine (v := 6) (l := p5298) (r := p5379) (m := 58293889578929932385) (k := 13) (by decide +kernel) c5298 c5379

def p5247 : Plan := .step 60 p5248 p5297
theorem c5247 : check p5247 59446811083536779361 13 = true := check_combine (v := 60) (l := p5248) (r := p5297) (m := 59446811083536779361) (k := 13) (by decide +kernel) c5248 c5297

def p5179 : Plan := .step 58 p5180 p5247
theorem c5179 : check p5179 59735041459688491105 13 = true := check_combine (v := 58) (l := p5180) (r := p5247) (m := 59735041459688491105) (k := 13) (by decide +kernel) c5180 c5247

def p5081 : Plan := .step 49 p5082 p5179
theorem c5081 : check p5081 59735604409641912417 13 = true := check_combine (v := 49) (l := p5082) (r := p5179) (m := 59735604409641912417) (k := 13) (by decide +kernel) c5082 c5179

def p4923 : Plan := .step 47 p4924 p5081
theorem c4923 : check p4923 59735745147130267745 13 = true := check_combine (v := 47) (l := p4924) (r := p5081) (m := 59735745147130267745) (k := 13) (by decide +kernel) c4924 c5081

def p4769 : Plan := .step 10 p4770 p4923
theorem c4769 : check p4769 59735745147130268769 13 = true := check_combine (v := 10) (l := p4770) (r := p4923) (m := 59735745147130268769) (k := 13) (by decide +kernel) c4770 c4923

def p4563 : Plan := .step 8 p4564 p4769
theorem c4563 : check p4563 59735745147130269025 13 = true := check_combine (v := 8) (l := p4564) (r := p4769) (m := 59735745147130269025) (k := 13) (by decide +kernel) c4564 c4769

def p4427 : Plan := .step 16 p4428 p4563
theorem c4427 : check p4427 59735745147130334561 13 = true := check_combine (v := 16) (l := p4428) (r := p4563) (m := 59735745147130334561) (k := 13) (by decide +kernel) c4428 c4563

def p5876 : Plan := .step 20 p5877 p5886
theorem c5876 : check p5876 54705201592779194400 12 = true := check_combine (v := 20) (l := p5877) (r := p5886) (m := 54705201592779194400) (k := 12) (by decide +kernel) c5877 c5886

def p5860 : Plan := .step 7 p5861 p5876
theorem c5860 : check p5860 54705201592779194528 12 = true := check_combine (v := 7) (l := p5861) (r := p5876) (m := 54705201592779194528) (k := 12) (by decide +kernel) c5861 c5876

def p5846 : Plan := .step 6 p5847 p5860
theorem c5846 : check p5846 54705201592779194592 12 = true := check_combine (v := 6) (l := p5847) (r := p5860) (m := 54705201592779194592) (k := 12) (by decide +kernel) c5847 c5860

def p5828 : Plan := .step 34 p5829 p5846
theorem c5828 : check p5828 54705201609959063776 12 = true := check_combine (v := 34) (l := p5829) (r := p5846) (m := 54705201609959063776) (k := 12) (by decide +kernel) c5829 c5846

def p5810 : Plan := .step 11 p5811 p5828
theorem c5810 : check p5810 54705201609959065824 12 = true := check_combine (v := 11) (l := p5811) (r := p5828) (m := 54705201609959065824) (k := 12) (by decide +kernel) c5811 c5828

def p6016 : Plan := .step 7 p6017 p6026
theorem c6016 : check p6016 53911431210532069794 12 = true := check_combine (v := 7) (l := p6017) (r := p6026) (m := 53911431210532069794) (k := 12) (by decide +kernel) c6017 c6026

def p6008 : Plan := .step 54 p6009 p6016
theorem c6008 : check p6008 53929445609041551778 12 = true := check_combine (v := 54) (l := p6009) (r := p6016) (m := 53929445609041551778) (k := 12) (by decide +kernel) c6009 c6016

def p5994 : Plan := .step 42 p5995 p6008
theorem c5994 : check p5994 53929450007088062882 12 = true := check_combine (v := 42) (l := p5995) (r := p6008) (m := 53929450007088062882) (k := 12) (by decide +kernel) c5995 c6008

def p5974 : Plan := .step 20 p5975 p5994
theorem c5974 : check p5974 53929450007089111458 12 = true := check_combine (v := 20) (l := p5975) (r := p5994) (m := 53929450007089111458) (k := 12) (by decide +kernel) c5975 c5994

def p5956 : Plan := .step 6 p5957 p5974
theorem c5956 : check p5956 53929450007089111522 12 = true := check_combine (v := 6) (l := p5957) (r := p5974) (m := 53929450007089111522) (k := 12) (by decide +kernel) c5957 c5974

def p5934 : Plan := .step 33 p5935 p5956
theorem c5934 : check p5934 53929450015679046114 12 = true := check_combine (v := 33) (l := p5935) (r := p5956) (m := 53929450015679046114) (k := 12) (by decide +kernel) c5935 c5956

def p6140 : Plan := .step 20 p6141 p6154
theorem c6140 : check p6140 55137087604070903970 12 = true := check_combine (v := 20) (l := p6141) (r := p6154) (m := 55137087604070903970) (k := 12) (by decide +kernel) c6141 c6154

def p6118 : Plan := .step 6 p6119 p6140
theorem c6118 : check p6118 55137087604070904034 12 = true := check_combine (v := 6) (l := p6119) (r := p6140) (m := 55137087604070904034) (k := 12) (by decide +kernel) c6119 c6140

def p6106 : Plan := .step 48 p6107 p6118
theorem c6106 : check p6106 55137369079047614690 12 = true := check_combine (v := 48) (l := p6107) (r := p6118) (m := 55137369079047614690) (k := 12) (by decide +kernel) c6107 c6118

def p6090 : Plan := .step 47 p6091 p6106
theorem c6090 : check p6090 55137509816535970018 12 = true := check_combine (v := 47) (l := p6091) (r := p6106) (m := 55137509816535970018) (k := 12) (by decide +kernel) c6091 c6106

def p6074 : Plan := .step 45 p6075 p6090
theorem c6074 : check p6074 55137545000908058850 12 = true := check_combine (v := 45) (l := p6075) (r := p6090) (m := 55137545000908058850) (k := 12) (by decide +kernel) c6075 c6090

def p6240 : Plan := .step 24 p6241 p6250
theorem c6240 : check p6240 55080795902984008160 12 = true := check_combine (v := 24) (l := p6241) (r := p6250) (m := 55080795902984008160) (k := 12) (by decide +kernel) c6241 c6250

def p6224 : Plan := .step 19 p6225 p6240
theorem c6224 : check p6224 55080795902984532448 12 = true := check_combine (v := 19) (l := p6225) (r := p6240) (m := 55080795902984532448) (k := 12) (by decide +kernel) c6225 c6240

def p6214 : Plan := .step 51 p6215 p6224
theorem c6214 : check p6214 55083047702798217696 12 = true := check_combine (v := 51) (l := p6215) (r := p6224) (m := 55083047702798217696) (k := 12) (by decide +kernel) c6215 c6224

def p6194 : Plan := .step 20 p6195 p6214
theorem c6194 : check p6194 55083047702799266272 12 = true := check_combine (v := 20) (l := p6195) (r := p6214) (m := 55083047702799266272) (k := 12) (by decide +kernel) c6195 c6214

def p6396 : Plan := .step 59 p6397 p6420
theorem c6396 : check p6396 9171244508444324256 12 = true := check_combine (v := 59) (l := p6397) (r := p6420) (m := 9171244508444324256) (k := 12) (by decide +kernel) c6397 c6420

def p6386 : Plan := .step 27 p6387 p6396
theorem c6386 : check p6386 9171244508578541984 12 = true := check_combine (v := 27) (l := p6387) (r := p6396) (m := 9171244508578541984) (k := 12) (by decide +kernel) c6387 c6396

def p6366 : Plan := .step 21 p6367 p6386
theorem c6366 : check p6366 9171244508580639136 12 = true := check_combine (v := 21) (l := p6367) (r := p6386) (m := 9171244508580639136) (k := 12) (by decide +kernel) c6367 c6386

def p6342 : Plan := .step 26 p6343 p6366
theorem c6342 : check p6342 9171244508647748000 12 = true := check_combine (v := 26) (l := p6343) (r := p6366) (m := 9171244508647748000) (k := 12) (by decide +kernel) c6343 c6366

def p6326 : Plan := .step 19 p6327 p6342
theorem c6326 : check p6326 9171244508648272288 12 = true := check_combine (v := 19) (l := p6327) (r := p6342) (m := 9171244508648272288) (k := 12) (by decide +kernel) c6327 c6342

def p6312 : Plan := .step 23 p6313 p6326
theorem c6312 : check p6312 9171244508656660896 12 = true := check_combine (v := 23) (l := p6313) (r := p6326) (m := 9171244508656660896) (k := 12) (by decide +kernel) c6313 c6326

def p6296 : Plan := .step 48 p6297 p6312
theorem c6296 : check p6296 9171525983633371552 12 = true := check_combine (v := 48) (l := p6297) (r := p6312) (m := 9171525983633371552) (k := 12) (by decide +kernel) c6297 c6312

def p6500 : Plan := .step 13 p6501 p6512
theorem c6500 : check p6500 54710503747083792418 12 = true := check_combine (v := 13) (l := p6501) (r := p6512) (m := 54710503747083792418) (k := 12) (by decide +kernel) c6501 c6512

def p6488 : Plan := .step 8 p6489 p6500
theorem c6488 : check p6488 54710503747083792674 12 = true := check_combine (v := 8) (l := p6489) (r := p6500) (m := 54710503747083792674) (k := 12) (by decide +kernel) c6489 c6500

def p6476 : Plan := .step 50 p6477 p6488
theorem c6476 : check p6476 54711629646990635298 12 = true := check_combine (v := 50) (l := p6477) (r := p6488) (m := 54711629646990635298) (k := 12) (by decide +kernel) c6477 c6488

def p6464 : Plan := .step 42 p6465 p6476
theorem c6464 : check p6464 54711634045037146402 12 = true := check_combine (v := 42) (l := p6465) (r := p6476) (m := 54711634045037146402) (k := 12) (by decide +kernel) c6465 c6476

def p6584 : Plan := .step 8 p6585 p6602
theorem c6584 : check p6584 37564400556583899426 12 = true := check_combine (v := 8) (l := p6585) (r := p6602) (m := 37564400556583899426) (k := 12) (by decide +kernel) c6585 c6602

def p6578 : Plan := .step 62 p6579 p6584
theorem c6578 : check p6578 42176086575011287330 12 = true := check_combine (v := 62) (l := p6579) (r := p6584) (m := 42176086575011287330) (k := 12) (by decide +kernel) c6579 c6584

def p6566 : Plan := .step 33 p6567 p6578
theorem c6566 : check p6566 42176086583601221922 12 = true := check_combine (v := 33) (l := p6567) (r := p6578) (m := 42176086583601221922) (k := 12) (by decide +kernel) c6567 c6578

def p6552 : Plan := .step 60 p6553 p6566
theorem c6552 : check p6552 43329008088208068898 12 = true := check_combine (v := 60) (l := p6553) (r := p6566) (m := 43329008088208068898) (k := 12) (by decide +kernel) c6553 c6566

def p6652 : Plan := .step 26 p6653 p6666
theorem c6652 : check p6652 9171421521418346786 12 = true := check_combine (v := 26) (l := p6653) (r := p6666) (m := 9171421521418346786) (k := 12) (by decide +kernel) c6653 c6666

def p6638 : Plan := .step 19 p6639 p6652
theorem c6638 : check p6638 9171421521418871074 12 = true := check_combine (v := 19) (l := p6639) (r := p6652) (m := 9171421521418871074) (k := 12) (by decide +kernel) c6639 c6652

def p6778 : Plan := .step 26 p6779 p6794
theorem c6778 : check p6778 44820508809583882530 12 = true := check_combine (v := 26) (l := p6779) (r := p6794) (m := 44820508809583882530) (k := 12) (by decide +kernel) c6779 c6794

def p6870 : Plan := .step 61 p6871 p6876
theorem c6870 : check p6870 48497407634332143650 12 = true := check_combine (v := 61) (l := p6871) (r := p6876) (m := 48497407634332143650) (k := 12) (by decide +kernel) c6871 c6876

def p7037 : Plan := .step 23 p7038 p7053
theorem c7037 : check p7037 53550450805697900578 13 = true := check_combine (v := 23) (l := p7038) (r := p7053) (m := 53550450805697900578) (k := 13) (by decide +kernel) c7038 c7053

def p7015 : Plan := .step 19 p7016 p7037
theorem c7015 : check p7015 53550450805698424866 13 = true := check_combine (v := 19) (l := p7016) (r := p7037) (m := 53550450805698424866) (k := 13) (by decide +kernel) c7016 c7037

def p6991 : Plan := .step 8 p6992 p7015
theorem c6991 : check p6991 53550450805698425122 13 = true := check_combine (v := 8) (l := p6992) (r := p7015) (m := 53550450805698425122) (k := 13) (by decide +kernel) c6992 c7015

def p6967 : Plan := .step 49 p6968 p6991
theorem c6967 : check p6967 53551013755651846434 13 = true := check_combine (v := 49) (l := p6968) (r := p6991) (m := 53551013755651846434) (k := 13) (by decide +kernel) c6968 c6991

def p6943 : Plan := .step 33 p6944 p6967
theorem c6943 : check p6943 53551013764241781026 13 = true := check_combine (v := 33) (l := p6944) (r := p6967) (m := 53551013764241781026) (k := 13) (by decide +kernel) c6944 c6967

def p6919 : Plan := .step 42 p6920 p6943
theorem c6919 : check p6919 53551018162288292130 13 = true := check_combine (v := 42) (l := p6920) (r := p6943) (m := 53551018162288292130) (k := 13) (by decide +kernel) c6920 c6943

def p6869 : Plan := .step 26 p6870 p6919
theorem c6869 : check p6869 53551018162355400994 13 = true := check_combine (v := 26) (l := p6870) (r := p6919) (m := 53551018162355400994) (k := 13) (by decide +kernel) c6870 c6919

def p6831 : Plan := .step 59 p6832 p6869
theorem c6831 : check p6831 54127478914658824482 13 = true := check_combine (v := 59) (l := p6832) (r := p6869) (m := 54127478914658824482) (k := 13) (by decide +kernel) c6832 c6869

def p6777 : Plan := .step 54 p6778 p6831
theorem c6777 : check p6777 54145493313168306466 13 = true := check_combine (v := 54) (l := p6778) (r := p6831) (m := 54145493313168306466) (k := 13) (by decide +kernel) c6778 c6831

def p6751 : Plan := .step 60 p6752 p6777
theorem c6751 : check p6751 55298414817775153442 13 = true := check_combine (v := 60) (l := p6752) (r := p6777) (m := 55298414817775153442) (k := 13) (by decide +kernel) c6752 c6777

def p6709 : Plan := .step 50 p6710 p6751
theorem c6709 : check p6709 55299540717681996066 13 = true := check_combine (v := 50) (l := p6710) (r := p6751) (m := 55299540717681996066) (k := 13) (by decide +kernel) c6710 c6751

def p6637 : Plan := .step 47 p6638 p6709
theorem c6637 : check p6637 55299681455170351394 13 = true := check_combine (v := 47) (l := p6638) (r := p6709) (m := 55299681455170351394) (k := 13) (by decide +kernel) c6638 c6709

def p6551 : Plan := .step 20 p6552 p6637
theorem c6551 : check p6551 55299681455171399970 13 = true := check_combine (v := 20) (l := p6552) (r := p6637) (m := 55299681455171399970) (k := 13) (by decide +kernel) c6552 c6637

def p6463 : Plan := .step 7 p6464 p6551
theorem c6463 : check p6463 55299681455171400098 13 = true := check_combine (v := 7) (l := p6464) (r := p6551) (m := 55299681455171400098) (k := 13) (by decide +kernel) c6464 c6551

def p6295 : Plan := .step 6 p6296 p6463
theorem c6295 : check p6295 55299681455171400162 13 = true := check_combine (v := 6) (l := p6296) (r := p6463) (m := 55299681455171400162) (k := 13) (by decide +kernel) c6296 c6463

def p6193 : Plan := .step 34 p6194 p6295
theorem c6193 : check p6193 55299681472351269346 13 = true := check_combine (v := 34) (l := p6194) (r := p6295) (m := 55299681472351269346) (k := 13) (by decide +kernel) c6194 c6295

def p6073 : Plan := .step 15 p6074 p6193
theorem c6073 : check p6073 55299681472351302114 13 = true := check_combine (v := 15) (l := p6074) (r := p6193) (m := 55299681472351302114) (k := 13) (by decide +kernel) c6074 c6193

def p5933 : Plan := .step 11 p5934 p6073
theorem c5933 : check p5933 55299681472351304162 13 = true := check_combine (v := 11) (l := p5934) (r := p6073) (m := 55299681472351304162) (k := 13) (by decide +kernel) c5934 c6073

def p5809 : Plan := .step 37 p5810 p5933
theorem c5809 : check p5809 55299681609790257634 13 = true := check_combine (v := 37) (l := p5810) (r := p5933) (m := 55299681609790257634) (k := 13) (by decide +kernel) c5810 c5933

def p7142 : Plan := .step 5 p7143 p7152
theorem c7142 : check p7142 51361834669851795619 12 = true := check_combine (v := 5) (l := p7143) (r := p7152) (m := 51361834669851795619) (k := 12) (by decide +kernel) c7143 c7152

def p7132 : Plan := .step 53 p7133 p7142
theorem c7132 : check p7132 51370841869106536611 12 = true := check_combine (v := 53) (l := p7133) (r := p7142) (m := 51370841869106536611) (k := 12) (by decide +kernel) c7133 c7142

def p7120 : Plan := .step 37 p7121 p7132
theorem c7120 : check p7120 51370842006545490083 12 = true := check_combine (v := 37) (l := p7121) (r := p7132) (m := 51370842006545490083) (k := 12) (by decide +kernel) c7121 c7132

def p7104 : Plan := .step 58 p7105 p7120
theorem c7104 : check p7104 51659072382697201827 12 = true := check_combine (v := 58) (l := p7105) (r := p7120) (m := 51659072382697201827) (k := 12) (by decide +kernel) c7105 c7120

def p7090 : Plan := .step 49 p7091 p7104
theorem c7090 : check p7090 51659635332650623139 12 = true := check_combine (v := 49) (l := p7091) (r := p7104) (m := 51659635332650623139) (k := 12) (by decide +kernel) c7091 c7104

def p7304 : Plan := .step 48 p7305 p7322
theorem c7304 : check p7304 53339227393925694400 12 = true := check_combine (v := 48) (l := p7305) (r := p7322) (m := 53339227393925694400) (k := 12) (by decide +kernel) c7305 c7322

def p7296 : Plan := .step 47 p7297 p7304
theorem c7296 : check p7296 53339368131414049728 12 = true := check_combine (v := 47) (l := p7297) (r := p7304) (m := 53339368131414049728) (k := 12) (by decide +kernel) c7297 c7304

def p7282 : Plan := .step 45 p7283 p7296
theorem c7282 : check p7282 53339403315786138560 12 = true := check_combine (v := 45) (l := p7283) (r := p7296) (m := 53339403315786138560) (k := 12) (by decide +kernel) c7283 c7296

def p7272 : Plan := .step 26 p7273 p7282
theorem c7272 : check p7272 53339403315853247424 12 = true := check_combine (v := 26) (l := p7273) (r := p7282) (m := 53339403315853247424) (k := 12) (by decide +kernel) c7273 c7282

def p7264 : Plan := .step 46 p7265 p7272
theorem c7264 : check p7264 53339473684597425088 12 = true := check_combine (v := 46) (l := p7265) (r := p7272) (m := 53339473684597425088) (k := 12) (by decide +kernel) c7265 c7272

def p7250 : Plan := .step 32 p7251 p7264
theorem c7250 : check p7250 53339473688892392384 12 = true := check_combine (v := 32) (l := p7251) (r := p7264) (m := 53339473688892392384) (k := 12) (by decide +kernel) c7251 c7264

def p7238 : Plan := .step 54 p7239 p7250
theorem c7238 : check p7238 53357488087401874368 12 = true := check_combine (v := 54) (l := p7239) (r := p7250) (m := 53357488087401874368) (k := 12) (by decide +kernel) c7239 c7250

def p7212 : Plan := .step 42 p7213 p7238
theorem c7212 : check p7212 53357492485448385472 12 = true := check_combine (v := 42) (l := p7213) (r := p7238) (m := 53357492485448385472) (k := 12) (by decide +kernel) c7213 c7238

def p7198 : Plan := .step 17 p7199 p7212
theorem c7198 : check p7198 53357492485448516544 12 = true := check_combine (v := 17) (l := p7199) (r := p7212) (m := 53357492485448516544) (k := 12) (by decide +kernel) c7199 c7212

def p7458 : Plan := .step 19 p7459 p7466
theorem c7458 : check p7458 53372282426660274881 12 = true := check_combine (v := 19) (l := p7459) (r := p7466) (m := 53372282426660274881) (k := 12) (by decide +kernel) c7459 c7466

def p7444 : Plan := .step 51 p7445 p7458
theorem c7444 : check p7444 53374534226473960129 12 = true := check_combine (v := 51) (l := p7445) (r := p7458) (m := 53374534226473960129) (k := 12) (by decide +kernel) c7445 c7458

def p7438 : Plan := .step 49 p7439 p7444
theorem c7438 : check p7438 53375097176427381441 12 = true := check_combine (v := 49) (l := p7439) (r := p7444) (m := 53375097176427381441) (k := 12) (by decide +kernel) c7439 c7444

def p7422 : Plan := .step 48 p7423 p7438
theorem c7422 : check p7422 53375378651404092097 12 = true := check_combine (v := 48) (l := p7423) (r := p7438) (m := 53375378651404092097) (k := 12) (by decide +kernel) c7423 c7438

def p7408 : Plan := .step 47 p7409 p7422
theorem c7408 : check p7408 53375519388892447425 12 = true := check_combine (v := 47) (l := p7409) (r := p7422) (m := 53375519388892447425) (k := 12) (by decide +kernel) c7409 c7422

def p7382 : Plan := .step 39 p7383 p7408
theorem c7382 : check p7382 53375519938648261313 12 = true := check_combine (v := 39) (l := p7383) (r := p7408) (m := 53375519938648261313) (k := 12) (by decide +kernel) c7383 c7408

def p7360 : Plan := .step 20 p7361 p7382
theorem c7360 : check p7360 53375519938649309889 12 = true := check_combine (v := 20) (l := p7361) (r := p7382) (m := 53375519938649309889) (k := 12) (by decide +kernel) c7361 c7382

def p7562 : Plan := .step 27 p7563 p7570
theorem c7562 : check p7562 5508417588022600643 12 = true := check_combine (v := 27) (l := p7563) (r := p7570) (m := 5508417588022600643) (k := 12) (by decide +kernel) c7563 c7570

def p7548 : Plan := .step 21 p7549 p7562
theorem c7548 : check p7548 5508417588024697795 12 = true := check_combine (v := 21) (l := p7549) (r := p7562) (m := 5508417588024697795) (k := 12) (by decide +kernel) c7549 c7562

def p7532 : Plan := .step 51 p7533 p7548
theorem c7532 : check p7532 5510669387838383043 12 = true := check_combine (v := 51) (l := p7533) (r := p7548) (m := 5510669387838383043) (k := 12) (by decide +kernel) c7533 c7548

def p7508 : Plan := .step 33 p7509 p7532
theorem c7508 : check p7508 5510669396428317635 12 = true := check_combine (v := 33) (l := p7509) (r := p7532) (m := 5510669396428317635) (k := 12) (by decide +kernel) c7509 c7532

def p7630 : Plan := .step 33 p7631 p7642
theorem c7630 : check p7630 53678668526613816194 12 = true := check_combine (v := 33) (l := p7631) (r := p7642) (m := 53678668526613816194) (k := 12) (by decide +kernel) c7631 c7642

def p7616 : Plan := .step 6 p7617 p7630
theorem c7616 : check p7616 53678668526613816258 12 = true := check_combine (v := 6) (l := p7617) (r := p7630) (m := 53678668526613816258) (k := 12) (by decide +kernel) c7617 c7630

def p7690 : Plan := .step 46 p7691 p7706
theorem c7690 : check p7690 53104287492572070849 12 = true := check_combine (v := 46) (l := p7691) (r := p7706) (m := 53104287492572070849) (k := 12) (by decide +kernel) c7691 c7706

def p7762 : Plan := .step 42 p7763 p7770
theorem c7762 : check p7762 12155694837394039363 12 = true := check_combine (v := 42) (l := p7763) (r := p7770) (m := 12155694837394039363) (k := 12) (by decide +kernel) c7763 c7770

def p7754 : Plan := .step 7 p7755 p7762
theorem c7754 : check p7754 12155694837394039491 12 = true := check_combine (v := 7) (l := p7755) (r := p7762) (m := 12155694837394039491) (k := 12) (by decide +kernel) c7755 c7762

def p7748 : Plan := .step 54 p7749 p7754
theorem c7748 : check p7748 12173709235903521475 12 = true := check_combine (v := 54) (l := p7749) (r := p7754) (m := 12173709235903521475) (k := 12) (by decide +kernel) c7749 c7754

def p7814 : Plan := .step 42 p7815 p7820
theorem c7814 : check p7814 53653973486862459651 12 = true := check_combine (v := 42) (l := p7815) (r := p7820) (m := 53653973486862459651) (k := 12) (by decide +kernel) c7815 c7820

def p7874 : Plan := .step 34 p7875 p7884
theorem c7874 : check p7874 637699830071386435 12 = true := check_combine (v := 34) (l := p7875) (r := p7884) (m := 637699830071386435) (k := 12) (by decide +kernel) c7875 c7884

def p7864 : Plan := .step 7 p7865 p7874
theorem c7864 : check p7864 637699830071386563 12 = true := check_combine (v := 7) (l := p7865) (r := p7874) (m := 637699830071386563) (k := 12) (by decide +kernel) c7865 c7874

def p7930 : Plan := .step 0 p7931 p7952
theorem c7930 : check p7930 44392175719186391491 12 = true := check_combine (v := 0) (l := p7931) (r := p7952) (m := 44392175719186391491) (k := 12) (by decide +kernel) c7931 c7952

def p8197 : Plan := .step 19 p8198 p8215
theorem c8197 : check p8197 49042423792378896898 13 = true := check_combine (v := 19) (l := p8198) (r := p8215) (m := 49042423792378896898) (k := 13) (by decide +kernel) c8198 c8215

def p8187 : Plan := .step 17 p8188 p8197
theorem c8187 : check p8187 49042423792379027970 13 = true := check_combine (v := 17) (l := p8188) (r := p8197) (m := 49042423792379027970) (k := 13) (by decide +kernel) c8188 c8197

def p8173 : Plan := .step 16 p8174 p8187
theorem c8173 : check p8173 49042423792379093506 13 = true := check_combine (v := 16) (l := p8174) (r := p8187) (m := 49042423792379093506) (k := 13) (by decide +kernel) c8174 c8187

def p8145 : Plan := .step 8 p8146 p8173
theorem c8145 : check p8145 49042423792379093762 13 = true := check_combine (v := 8) (l := p8146) (r := p8173) (m := 49042423792379093762) (k := 13) (by decide +kernel) c8146 c8173

def p8127 : Plan := .step 62 p8128 p8145
theorem c8127 : check p8127 53654109810806481666 13 = true := check_combine (v := 62) (l := p8128) (r := p8145) (m := 53654109810806481666) (k := 13) (by decide +kernel) c8128 c8145

def p8107 : Plan := .step 34 p8108 p8127
theorem c8107 : check p8107 53654109827986350850 13 = true := check_combine (v := 34) (l := p8108) (r := p8127) (m := 53654109827986350850) (k := 13) (by decide +kernel) c8108 c8127

def p8091 : Plan := .step 20 p8092 p8107
theorem c8091 : check p8091 53654109827987399426 13 = true := check_combine (v := 20) (l := p8092) (r := p8107) (m := 53654109827987399426) (k := 13) (by decide +kernel) c8092 c8107

def p8073 : Plan := .step 0 p8074 p8091
theorem c8073 : check p8073 53654109827987399427 13 = true := check_combine (v := 0) (l := p8074) (r := p8091) (m := 53654109827987399427) (k := 13) (by decide +kernel) c8074 c8091

def p8029 : Plan := .step 7 p8030 p8073
theorem c8029 : check p8029 53654109827987399555 13 = true := check_combine (v := 7) (l := p8030) (r := p8073) (m := 53654109827987399555) (k := 13) (by decide +kernel) c8030 c8073

def p7989 : Plan := .step 6 p7990 p8029
theorem c7989 : check p7989 53654109827987399619 13 = true := check_combine (v := 6) (l := p7990) (r := p8029) (m := 53654109827987399619) (k := 13) (by decide +kernel) c7990 c8029

def p7929 : Plan := .step 54 p7930 p7989
theorem c7929 : check p7929 53672124226496881603 13 = true := check_combine (v := 54) (l := p7930) (r := p7989) (m := 53672124226496881603) (k := 13) (by decide +kernel) c7930 c7989

def p7863 : Plan := .step 42 p7864 p7929
theorem c7863 : check p7863 53672128624543392707 13 = true := check_combine (v := 42) (l := p7864) (r := p7929) (m := 53672128624543392707) (k := 13) (by decide +kernel) c7864 c7929

def p7813 : Plan := .step 53 p7814 p7863
theorem c7813 : check p7813 53681135823798133699 13 = true := check_combine (v := 53) (l := p7814) (r := p7863) (m := 53681135823798133699) (k := 13) (by decide +kernel) c7814 c7863

def p7747 : Plan := .step 46 p7748 p7813
theorem c7747 : check p7747 53681206192542311363 13 = true := check_combine (v := 46) (l := p7748) (r := p7813) (m := 53681206192542311363) (k := 13) (by decide +kernel) c7748 c7813

def p7689 : Plan := .step 33 p7690 p7747
theorem c7689 : check p7689 53681206201132245955 13 = true := check_combine (v := 33) (l := p7690) (r := p7747) (m := 53681206201132245955) (k := 13) (by decide +kernel) c7690 c7747

def p7615 : Plan := .step 58 p7616 p7689
theorem c7615 : check p7615 53969436577283957699 13 = true := check_combine (v := 58) (l := p7616) (r := p7689) (m := 53969436577283957699) (k := 13) (by decide +kernel) c7616 c7689

def p7507 : Plan := .step 49 p7508 p7615
theorem c7507 : check p7507 53969999527237379011 13 = true := check_combine (v := 49) (l := p7508) (r := p7615) (m := 53969999527237379011) (k := 13) (by decide +kernel) c7508 c7615

def p7359 : Plan := .step 37 p7360 p7507
theorem c7359 : check p7359 53969999664676332483 13 = true := check_combine (v := 37) (l := p7360) (r := p7507) (m := 53969999664676332483) (k := 13) (by decide +kernel) c7360 c7507

def p7197 : Plan := .step 5 p7198 p7359
theorem c7197 : check p7197 53969999664676332515 13 = true := check_combine (v := 5) (l := p7198) (r := p7359) (m := 53969999664676332515) (k := 13) (by decide +kernel) c7198 c7359

def p7089 : Plan := .step 40 p7090 p7197
theorem c7089 : check p7089 53970000764187960291 13 = true := check_combine (v := 40) (l := p7090) (r := p7197) (m := 53970000764187960291) (k := 13) (by decide +kernel) c7090 c7197

def p8328 : Plan := .step 26 p8329 p8338
theorem c8328 : check p8328 73011804878317372096 12 = true := check_combine (v := 26) (l := p8329) (r := p8338) (m := 73011804878317372096) (k := 12) (by decide +kernel) c8329 c8338

def p8314 : Plan := .step 48 p8315 p8328
theorem c8314 : check p8314 73012086353294082752 12 = true := check_combine (v := 48) (l := p8315) (r := p8328) (m := 73012086353294082752) (k := 12) (by decide +kernel) c8315 c8328

def p8302 : Plan := .step 47 p8303 p8314
theorem c8302 : check p8302 73012227090782438080 12 = true := check_combine (v := 47) (l := p8303) (r := p8314) (m := 73012227090782438080) (k := 12) (by decide +kernel) c8303 c8314

def p8282 : Plan := .step 46 p8283 p8302
theorem c8282 : check p8282 73012297459526615744 12 = true := check_combine (v := 46) (l := p8283) (r := p8302) (m := 73012297459526615744) (k := 12) (by decide +kernel) c8283 c8302

def p8264 : Plan := .step 45 p8265 p8282
theorem c8264 : check p8264 73012332643898704576 12 = true := check_combine (v := 45) (l := p8265) (r := p8282) (m := 73012332643898704576) (k := 12) (by decide +kernel) c8265 c8282

def p8426 : Plan := .step 47 p8427 p8442
theorem c8426 : check p8426 55176283702610452994 12 = true := check_combine (v := 47) (l := p8427) (r := p8442) (m := 55176283702610452994) (k := 12) (by decide +kernel) c8427 c8442

def p8416 : Plan := .step 35 p8417 p8426
theorem c8416 : check p8416 55176283736970191362 12 = true := check_combine (v := 35) (l := p8417) (r := p8426) (m := 55176283736970191362) (k := 12) (by decide +kernel) c8417 c8426

def p8406 : Plan := .step 26 p8407 p8416
theorem c8406 : check p8406 55176283737037300226 12 = true := check_combine (v := 26) (l := p8407) (r := p8416) (m := 55176283737037300226) (k := 12) (by decide +kernel) c8407 c8416

def p8392 : Plan := .step 21 p8393 p8406
theorem c8392 : check p8392 55176283737039397378 12 = true := check_combine (v := 21) (l := p8393) (r := p8406) (m := 55176283737039397378) (k := 12) (by decide +kernel) c8393 c8406

def p8382 : Plan := .step 46 p8383 p8392
theorem c8382 : check p8382 55176354105783575042 12 = true := check_combine (v := 46) (l := p8383) (r := p8392) (m := 55176354105783575042) (k := 12) (by decide +kernel) c8383 c8392

def p8532 : Plan := .step 1 p8533 p8550
theorem c8532 : check p8532 13670113908150317763 12 = true := check_combine (v := 1) (l := p8533) (r := p8550) (m := 13670113908150317763) (k := 12) (by decide +kernel) c8533 c8550

def p8522 : Plan := .step 40 p8523 p8532
theorem c8522 : check p8522 13670115007661945539 12 = true := check_combine (v := 40) (l := p8523) (r := p8532) (m := 13670115007661945539) (k := 12) (by decide +kernel) c8523 c8532

def p8508 : Plan := .step 14 p8509 p8522
theorem c8508 : check p8508 13670115007661961923 12 = true := check_combine (v := 14) (l := p8509) (r := p8522) (m := 13670115007661961923) (k := 12) (by decide +kernel) c8509 c8522

def p8492 : Plan := .step 48 p8493 p8508
theorem c8492 : check p8492 13670396482638672579 12 = true := check_combine (v := 48) (l := p8493) (r := p8508) (m := 13670396482638672579) (k := 12) (by decide +kernel) c8493 c8508

def p8480 : Plan := .step 47 p8481 p8492
theorem c8480 : check p8480 13670537220127027907 12 = true := check_combine (v := 47) (l := p8481) (r := p8492) (m := 13670537220127027907) (k := 12) (by decide +kernel) c8481 c8492

def p8618 : Plan := .step 58 p8619 p8630
theorem c8618 : check p8618 6707840825408709315 12 = true := check_combine (v := 58) (l := p8619) (r := p8630) (m := 6707840825408709315) (k := 12) (by decide +kernel) c8619 c8630

def p8606 : Plan := .step 35 p8607 p8618
theorem c8606 : check p8606 6707840859768447683 12 = true := check_combine (v := 35) (l := p8607) (r := p8618) (m := 6707840859768447683) (k := 12) (by decide +kernel) c8607 c8618

def p8598 : Plan := .step 26 p8599 p8606
theorem c8598 : check p8598 6707840859835556547 12 = true := check_combine (v := 26) (l := p8599) (r := p8606) (m := 6707840859835556547) (k := 12) (by decide +kernel) c8599 c8606

def p8586 : Plan := .step 61 p8587 p8598
theorem c8586 : check p8586 9013683869049250499 12 = true := check_combine (v := 61) (l := p8587) (r := p8598) (m := 9013683869049250499) (k := 12) (by decide +kernel) c8587 c8598

def p8698 : Plan := .step 35 p8699 p8712
theorem c8698 : check p8698 9925381318546121219 12 = true := check_combine (v := 35) (l := p8699) (r := p8712) (m := 9925381318546121219) (k := 12) (by decide +kernel) c8699 c8712

def p8684 : Plan := .step 26 p8685 p8698
theorem c8684 : check p8684 9925381318613230083 12 = true := check_combine (v := 26) (l := p8685) (r := p8698) (m := 9925381318613230083) (k := 12) (by decide +kernel) c8685 c8698

def p8674 : Plan := .step 6 p8675 p8684
theorem c8674 : check p8674 9925381318613230147 12 = true := check_combine (v := 6) (l := p8675) (r := p8684) (m := 9925381318613230147) (k := 12) (by decide +kernel) c8675 c8684

def p8748 : Plan := .step 1 p8749 p8768
theorem c8748 : check p8748 50268054431079420611 12 = true := check_combine (v := 1) (l := p8749) (r := p8768) (m := 50268054431079420611) (k := 12) (by decide +kernel) c8749 c8768

def p8850 : Plan := .step 19 p8851 p8858
theorem c8850 : check p8850 69012044294319059458 12 = true := check_combine (v := 19) (l := p8851) (r := p8858) (m := 69012044294319059458) (k := 12) (by decide +kernel) c8851 c8858

def p9081 : Plan := .step 20 p9082 p9095
theorem c9081 : check p9081 72469682461556634177 13 = true := check_combine (v := 20) (l := p9082) (r := p9095) (m := 72469682461556634177) (k := 13) (by decide +kernel) c9082 c9095

def p9065 : Plan := .step 16 p9066 p9081
theorem c9065 : check p9065 72469682461556699713 13 = true := check_combine (v := 16) (l := p9066) (r := p9081) (m := 72469682461556699713) (k := 13) (by decide +kernel) c9066 c9081

def p9055 : Plan := .step 60 p9056 p9065
theorem c9055 : check p9055 73622603966163546689 13 = true := check_combine (v := 60) (l := p9056) (r := p9065) (m := 73622603966163546689) (k := 13) (by decide +kernel) c9056 c9065

def p9045 : Plan := .step 49 p9046 p9055
theorem c9045 : check p9045 73623166916116968001 13 = true := check_combine (v := 49) (l := p9046) (r := p9055) (m := 73623166916116968001) (k := 13) (by decide +kernel) c9046 c9055

def p9023 : Plan := .step 7 p9024 p9045
theorem c9023 : check p9023 73623166916116968129 13 = true := check_combine (v := 7) (l := p9024) (r := p9045) (m := 73623166916116968129) (k := 13) (by decide +kernel) c9024 c9045

def p9005 : Plan := .step 39 p9006 p9023
theorem c9005 : check p9005 73623167465872782017 13 = true := check_combine (v := 39) (l := p9006) (r := p9023) (m := 73623167465872782017) (k := 13) (by decide +kernel) c9006 c9023

def p8971 : Plan := .step 19 p8972 p9005
theorem c8971 : check p8971 73623167465873306305 13 = true := check_combine (v := 19) (l := p8972) (r := p9005) (m := 73623167465873306305) (k := 13) (by decide +kernel) c8972 c9005

def p8939 : Plan := .step 1 p8940 p8971
theorem c8939 : check p8939 73623167465873306307 13 = true := check_combine (v := 1) (l := p8940) (r := p8971) (m := 73623167465873306307) (k := 13) (by decide +kernel) c8940 c8971

def p8903 : Plan := .step 50 p8904 p8939
theorem c8903 : check p8903 73624293365780148931 13 = true := check_combine (v := 50) (l := p8904) (r := p8939) (m := 73624293365780148931) (k := 13) (by decide +kernel) c8904 c8939

def p8849 : Plan := .step 18 p8850 p8903
theorem c8849 : check p8849 73624293365780411075 13 = true := check_combine (v := 18) (l := p8850) (r := p8903) (m := 73624293365780411075) (k := 13) (by decide +kernel) c8850 c8903

def p8815 : Plan := .step 40 p8816 p8849
theorem c8815 : check p8815 73624294465292038851 13 = true := check_combine (v := 40) (l := p8816) (r := p8849) (m := 73624294465292038851) (k := 13) (by decide +kernel) c8816 c8849

def p8747 : Plan := .step 26 p8748 p8815
theorem c8747 : check p8747 73624294465359147715 13 = true := check_combine (v := 26) (l := p8748) (r := p8815) (m := 73624294465359147715) (k := 13) (by decide +kernel) c8748 c8815

def p8673 : Plan := .step 48 p8674 p8747
theorem c8673 : check p8673 73624575940335858371 13 = true := check_combine (v := 48) (l := p8674) (r := p8747) (m := 73624575940335858371) (k := 13) (by decide +kernel) c8674 c8747

def p8585 : Plan := .step 47 p8586 p8673
theorem c8585 : check p8585 73624716677824213699 13 = true := check_combine (v := 47) (l := p8586) (r := p8673) (m := 73624716677824213699) (k := 13) (by decide +kernel) c8586 c8673

def p8479 : Plan := .step 46 p8480 p8585
theorem c8479 : check p8479 73624787046568391363 13 = true := check_combine (v := 46) (l := p8480) (r := p8585) (m := 73624787046568391363) (k := 13) (by decide +kernel) c8480 c8585

def p8381 : Plan := .step 45 p8382 p8479
theorem c8381 : check p8381 73624822230940480195 13 = true := check_combine (v := 45) (l := p8382) (r := p8479) (m := 73624822230940480195) (k := 13) (by decide +kernel) c8382 c8479

def p8263 : Plan := .step 5 p8264 p8381
theorem c8263 : check p8263 73624822230940480227 13 = true := check_combine (v := 5) (l := p8264) (r := p8381) (m := 73624822230940480227) (k := 13) (by decide +kernel) c8264 c8381

def p9194 : Plan := .step 17 p9195 p9200
theorem c9194 : check p9194 55158269443549061410 12 = true := check_combine (v := 17) (l := p9195) (r := p9200) (m := 55158269443549061410) (k := 12) (by decide +kernel) c9195 c9200

def p9184 : Plan := .step 35 p9185 p9194
theorem c9184 : check p9184 55158269477908799778 12 = true := check_combine (v := 35) (l := p9185) (r := p9194) (m := 55158269477908799778) (k := 12) (by decide +kernel) c9185 c9194

def p9172 : Plan := .step 9 p9173 p9184
theorem c9172 : check p9172 55158269477908800290 12 = true := check_combine (v := 9) (l := p9173) (r := p9184) (m := 55158269477908800290) (k := 12) (by decide +kernel) c9173 c9184

def p9164 : Plan := .step 26 p9165 p9172
theorem c9164 : check p9164 55158269477975909154 12 = true := check_combine (v := 26) (l := p9165) (r := p9172) (m := 55158269477975909154) (k := 12) (by decide +kernel) c9165 c9172

def p9146 : Plan := .step 21 p9147 p9164
theorem c9146 : check p9146 55158269477978006306 12 = true := check_combine (v := 21) (l := p9147) (r := p9164) (m := 55158269477978006306) (k := 12) (by decide +kernel) c9147 c9164

def p9134 : Plan := .step 46 p9135 p9146
theorem c9134 : check p9134 55158339846722183970 12 = true := check_combine (v := 46) (l := p9135) (r := p9146) (m := 55158339846722183970) (k := 12) (by decide +kernel) c9135 c9146

def p9264 : Plan := .step 47 p9265 p9276
theorem c9264 : check p9264 13652527361259630818 12 = true := check_combine (v := 47) (l := p9265) (r := p9276) (m := 13652527361259630818) (k := 12) (by decide +kernel) c9265 c9276

def p9246 : Plan := .step 9 p9247 p9264
theorem c9246 : check p9246 13652527361259631330 12 = true := check_combine (v := 9) (l := p9247) (r := p9264) (m := 13652527361259631330) (k := 12) (by decide +kernel) c9247 c9264

def p9340 : Plan := .step 26 p9341 p9358
theorem c9340 : check p9340 6437629415392960994 12 = true := check_combine (v := 26) (l := p9341) (r := p9358) (m := 6437629415392960994) (k := 12) (by decide +kernel) c9341 c9358

def p9332 : Plan := .step 9 p9333 p9340
theorem c9332 : check p9332 6437629415392961506 12 = true := check_combine (v := 9) (l := p9333) (r := p9340) (m := 6437629415392961506) (k := 12) (by decide +kernel) c9333 c9340

def p9326 : Plan := .step 61 p9327 p9332
theorem c9326 : check p9326 8743472424606655458 12 = true := check_combine (v := 61) (l := p9327) (r := p9332) (m := 8743472424606655458) (k := 12) (by decide +kernel) c9327 c9332

def p9318 : Plan := .step 58 p9319 p9326
theorem c9318 : check p9318 9031702800758367202 12 = true := check_combine (v := 58) (l := p9319) (r := p9326) (m := 9031702800758367202) (k := 12) (by decide +kernel) c9319 c9326

def p9442 : Plan := .step 26 p9443 p9454
theorem c9442 : check p9442 9889357059093061922 12 = true := check_combine (v := 26) (l := p9443) (r := p9454) (m := 9889357059093061922) (k := 12) (by decide +kernel) c9443 c9454

def p9418 : Plan := .step 9 p9419 p9442
theorem c9418 : check p9418 9889357059093062434 12 = true := check_combine (v := 9) (l := p9419) (r := p9442) (m := 9889357059093062434) (k := 12) (by decide +kernel) c9419 c9442

def p9402 : Plan := .step 6 p9403 p9418
theorem c9402 : check p9402 9889357059093062498 12 = true := check_combine (v := 6) (l := p9403) (r := p9418) (m := 9889357059093062498) (k := 12) (by decide +kernel) c9403 c9418

def p9540 : Plan := .step 6 p9541 p9556
theorem c9540 : check p9540 49025065473567248608 12 = true := check_combine (v := 6) (l := p9541) (r := p9556) (m := 49025065473567248608) (k := 12) (by decide +kernel) c9541 c9556

def p9536 : Plan := .step 60 p9537 p9540
theorem c9536 : check p9536 50177986978174095584 12 = true := check_combine (v := 60) (l := p9537) (r := p9540) (m := 50177986978174095584) (k := 12) (by decide +kernel) c9537 c9540

def p9528 : Plan := .step 56 p9529 p9536
theorem c9528 : check p9528 50250044572212023520 12 = true := check_combine (v := 56) (l := p9529) (r := p9536) (m := 50250044572212023520) (k := 12) (by decide +kernel) c9529 c9536

def p9508 : Plan := .step 1 p9509 p9528
theorem c9508 : check p9508 50250044572212023522 12 = true := check_combine (v := 1) (l := p9509) (r := p9528) (m := 50250044572212023522) (k := 12) (by decide +kernel) c9509 c9528

def p9492 : Plan := .step 9 p9493 p9508
theorem c9492 : check p9492 50250044572212024034 12 = true := check_combine (v := 9) (l := p9493) (r := p9508) (m := 50250044572212024034) (k := 12) (by decide +kernel) c9493 c9508

def p9867 : Plan := .step 7 p9868 p9879
theorem c9867 : check p9867 63228863513103987168 13 = true := check_combine (v := 7) (l := p9868) (r := p9879) (m := 63228863513103987168) (k := 13) (by decide +kernel) c9868 c9879

def p9857 : Plan := .step 63 p9858 p9867
theorem c9857 : check p9857 72452235549958762976 13 = true := check_combine (v := 63) (l := p9858) (r := p9867) (m := 72452235549958762976) (k := 13) (by decide +kernel) c9858 c9867

def p9833 : Plan := .step 39 p9834 p9857
theorem c9833 : check p9833 72452236099714576864 13 = true := check_combine (v := 39) (l := p9834) (r := p9857) (m := 72452236099714576864) (k := 13) (by decide +kernel) c9834 c9857

def p9815 : Plan := .step 29 p9816 p9833
theorem c9815 : check p9815 72452236100251447776 13 = true := check_combine (v := 29) (l := p9816) (r := p9833) (m := 72452236100251447776) (k := 13) (by decide +kernel) c9816 c9833

def p9787 : Plan := .step 9 p9788 p9815
theorem c9787 : check p9787 72452236100251448288 13 = true := check_combine (v := 9) (l := p9788) (r := p9815) (m := 72452236100251448288) (k := 13) (by decide +kernel) c9788 c9815

def p9771 : Plan := .step 1 p9772 p9787
theorem c9771 : check p9771 72452236100251448290 13 = true := check_combine (v := 1) (l := p9772) (r := p9787) (m := 72452236100251448290) (k := 13) (by decide +kernel) c9772 c9787

def p9751 : Plan := .step 60 p9752 p9771
theorem c9751 : check p9751 73605157604858295266 13 = true := check_combine (v := 60) (l := p9752) (r := p9771) (m := 73605157604858295266) (k := 13) (by decide +kernel) c9752 c9771

def p9717 : Plan := .step 50 p9718 p9751
theorem c9717 : check p9717 73606283504765137890 13 = true := check_combine (v := 50) (l := p9718) (r := p9751) (m := 73606283504765137890) (k := 13) (by decide +kernel) c9718 c9751

def p9675 : Plan := .step 18 p9676 p9717
theorem c9675 : check p9675 73606283504765400034 13 = true := check_combine (v := 18) (l := p9676) (r := p9717) (m := 73606283504765400034) (k := 13) (by decide +kernel) c9676 c9717

def p9631 : Plan := .step 17 p9632 p9675
theorem c9631 : check p9631 73606283504765531106 13 = true := check_combine (v := 17) (l := p9632) (r := p9675) (m := 73606283504765531106) (k := 13) (by decide +kernel) c9632 c9675

def p9589 : Plan := .step 40 p9590 p9631
theorem c9589 : check p9589 73606284604277158882 13 = true := check_combine (v := 40) (l := p9590) (r := p9631) (m := 73606284604277158882) (k := 13) (by decide +kernel) c9590 c9631

def p9491 : Plan := .step 26 p9492 p9589
theorem c9491 : check p9491 73606284604344267746 13 = true := check_combine (v := 26) (l := p9492) (r := p9589) (m := 73606284604344267746) (k := 13) (by decide +kernel) c9492 c9589

def p9401 : Plan := .step 48 p9402 p9491
theorem c9401 : check p9401 73606566079320978402 13 = true := check_combine (v := 48) (l := p9402) (r := p9491) (m := 73606566079320978402) (k := 13) (by decide +kernel) c9402 c9491

def p9317 : Plan := .step 47 p9318 p9401
theorem c9317 : check p9317 73606706816809333730 13 = true := check_combine (v := 47) (l := p9318) (r := p9401) (m := 73606706816809333730) (k := 13) (by decide +kernel) c9318 c9401

def p9245 : Plan := .step 46 p9246 p9317
theorem c9245 : check p9245 73606777185553511394 13 = true := check_combine (v := 46) (l := p9246) (r := p9317) (m := 73606777185553511394) (k := 13) (by decide +kernel) c9246 c9317

def p9133 : Plan := .step 45 p9134 p9245
theorem c9133 : check p9133 73606812369925600226 13 = true := check_combine (v := 45) (l := p9134) (r := p9245) (m := 73606812369925600226) (k := 13) (by decide +kernel) c9134 c9245

def p9952 : Plan := .step 53 p9953 p9960
theorem c9952 : check p9952 72669534046843175872 12 = true := check_combine (v := 53) (l := p9953) (r := p9960) (m := 72669534046843175872) (k := 12) (by decide +kernel) c9953 c9960

def p9946 : Plan := .step 32 p9947 p9952
theorem c9946 : check p9946 72669534051138143168 12 = true := check_combine (v := 32) (l := p9947) (r := p9952) (m := 72669534051138143168) (k := 12) (by decide +kernel) c9947 c9952

def p9938 : Plan := .step 58 p9939 p9946
theorem c9938 : check p9938 72957764427289854912 12 = true := check_combine (v := 58) (l := p9939) (r := p9946) (m := 72957764427289854912) (k := 12) (by decide +kernel) c9939 c9946

def p9924 : Plan := .step 46 p9925 p9938
theorem c9924 : check p9924 72957834796034032576 12 = true := check_combine (v := 46) (l := p9925) (r := p9938) (m := 72957834796034032576) (k := 12) (by decide +kernel) c9925 c9938

def p10054 : Plan := .step 53 p10055 p10068
theorem c10054 : check p10054 13021050195468497601 12 = true := check_combine (v := 53) (l := p10055) (r := p10068) (m := 13021050195468497601) (k := 12) (by decide +kernel) c10055 c10068

def p10050 : Plan := .step 59 p10051 p10054
theorem c10050 : check p10050 13597510947771921089 12 = true := check_combine (v := 59) (l := p10051) (r := p10054) (m := 13597510947771921089) (k := 12) (by decide +kernel) c10051 c10054

def p10042 : Plan := .step 49 p10043 p10050
theorem c10042 : check p10042 13598073897725342401 12 = true := check_combine (v := 49) (l := p10043) (r := p10050) (m := 13598073897725342401) (k := 12) (by decide +kernel) c10043 c10050

def p10028 : Plan := .step 42 p10029 p10042
theorem c10028 : check p10028 13598078295771853505 12 = true := check_combine (v := 42) (l := p10029) (r := p10042) (m := 13598078295771853505) (k := 12) (by decide +kernel) c10029 c10042

def p10016 : Plan := .step 54 p10017 p10028
theorem c10016 : check p10016 13616092694281335489 12 = true := check_combine (v := 54) (l := p10017) (r := p10028) (m := 13616092694281335489) (k := 12) (by decide +kernel) c10017 c10028

def p10002 : Plan := .step 32 p10003 p10016
theorem c10002 : check p10002 13616092698576302785 12 = true := check_combine (v := 32) (l := p10003) (r := p10016) (m := 13616092698576302785) (k := 12) (by decide +kernel) c10003 c10016

def p10122 : Plan := .step 43 p10123 p10136
theorem c10122 : check p10122 25110976522641486785 12 = true := check_combine (v := 43) (l := p10123) (r := p10136) (m := 25110976522641486785) (k := 12) (by decide +kernel) c10123 c10136

def p10106 : Plan := .step 37 p10107 p10122
theorem c10106 : check p10106 25110976660080440257 12 = true := check_combine (v := 37) (l := p10107) (r := p10122) (m := 25110976660080440257) (k := 12) (by decide +kernel) c10107 c10122

def p10226 : Plan := .step 43 p10227 p10230
theorem c10226 : check p10226 72686998554385580737 12 = true := check_combine (v := 43) (l := p10227) (r := p10230) (m := 72686998554385580737) (k := 12) (by decide +kernel) c10227 c10230

def p10280 : Plan := .step 43 p10281 p10298
theorem c10280 : check p10280 67489849020492034817 12 = true := check_combine (v := 43) (l := p10281) (r := p10298) (m := 67489849020492034817) (k := 12) (by decide +kernel) c10281 c10298

def p10278 : Plan := .step 62 p10279 p10280
theorem c10278 : check p10278 72101535038919422721 12 = true := check_combine (v := 62) (l := p10279) (r := p10280) (m := 72101535038919422721) (k := 12) (by decide +kernel) c10279 c10280

def p10463 : Plan := .step 19 p10464 p10473
theorem c10463 : check p10463 59435152219515532225 13 = true := check_combine (v := 19) (l := p10464) (r := p10473) (m := 59435152219515532225) (k := 13) (by decide +kernel) c10464 c10473

def p10451 : Plan := .step 63 p10452 p10463
theorem c10451 : check p10451 68658524256370308033 13 = true := check_combine (v := 63) (l := p10452) (r := p10463) (m := 68658524256370308033) (k := 13) (by decide +kernel) c10452 c10463

def p10437 : Plan := .step 51 p10438 p10451
theorem c10437 : check p10437 68660776056183993281 13 = true := check_combine (v := 51) (l := p10438) (r := p10451) (m := 68660776056183993281) (k := 13) (by decide +kernel) c10438 c10451

def p10403 : Plan := .step 32 p10404 p10437
theorem c10403 : check p10403 68660776060478960577 13 = true := check_combine (v := 32) (l := p10404) (r := p10437) (m := 68660776060478960577) (k := 13) (by decide +kernel) c10404 c10437

def p10391 : Plan := .step 62 p10392 p10403
theorem c10391 : check p10391 73272462078906348481 13 = true := check_combine (v := 62) (l := p10392) (r := p10403) (m := 73272462078906348481) (k := 13) (by decide +kernel) c10392 c10403

def p10367 : Plan := .step 43 p10368 p10391
theorem c10367 : check p10367 73272470874999370689 13 = true := check_combine (v := 43) (l := p10368) (r := p10391) (m := 73272470874999370689) (k := 13) (by decide +kernel) c10368 c10391

def p10331 : Plan := .step 36 p10332 p10367
theorem c10331 : check p10331 73272470943718847425 13 = true := check_combine (v := 36) (l := p10332) (r := p10367) (m := 73272470943718847425) (k := 13) (by decide +kernel) c10332 c10367

def p10277 : Plan := .step 53 p10278 p10331
theorem c10277 : check p10277 73281478142973588417 13 = true := check_combine (v := 53) (l := p10278) (r := p10331) (m := 73281478142973588417) (k := 13) (by decide +kernel) c10278 c10331

def p10225 : Plan := .step 37 p10226 p10277
theorem c10225 : check p10225 73281478280412541889 13 = true := check_combine (v := 37) (l := p10226) (r := p10277) (m := 73281478280412541889) (k := 13) (by decide +kernel) c10226 c10277

def p10179 : Plan := .step 58 p10180 p10225
theorem c10179 : check p10179 73569708656564253633 13 = true := check_combine (v := 58) (l := p10180) (r := p10225) (m := 73569708656564253633) (k := 13) (by decide +kernel) c10180 c10225

def p10105 : Plan := .step 49 p10106 p10179
theorem c10105 : check p10105 73570271606517674945 13 = true := check_combine (v := 49) (l := p10106) (r := p10179) (m := 73570271606517674945) (k := 13) (by decide +kernel) c10106 c10179

def p10001 : Plan := .step 46 p10002 p10105
theorem c10001 : check p10001 73570341975261852609 13 = true := check_combine (v := 46) (l := p10002) (r := p10105) (m := 73570341975261852609) (k := 13) (by decide +kernel) c10002 c10105

def p9923 : Plan := .step 5 p9924 p10001
theorem c9923 : check p9923 73570341975261852641 13 = true := check_combine (v := 5) (l := p9924) (r := p10001) (m := 73570341975261852641) (k := 13) (by decide +kernel) c9924 c10001

def p10522 : Plan := .step 5 p10523 p10534
theorem c10522 : check p10522 12605917623086903330 12 = true := check_combine (v := 5) (l := p10523) (r := p10534) (m := 12605917623086903330) (k := 12) (by decide +kernel) c10523 c10534

def p10762 : Plan := .step 1 p10763 p10770
theorem c10762 : check p10762 12079643117077799107 12 = true := check_combine (v := 1) (l := p10763) (r := p10770) (m := 12079643117077799107) (k := 12) (by decide +kernel) c10763 c10770

def p10929 : Plan := .step 13 p10930 p10949
theorem c10929 : check p10929 10931946491740959363 13 = true := check_combine (v := 13) (l := p10930) (r := p10949) (m := 10931946491740959363) (k := 13) (by decide +kernel) c10930 c10949

def p10915 : Plan := .step 61 p10916 p10929
theorem c10915 : check p10915 13237789500954653315 13 = true := check_combine (v := 61) (l := p10916) (r := p10929) (m := 13237789500954653315) (k := 13) (by decide +kernel) c10916 c10929

def p10905 : Plan := .step 47 p10906 p10915
theorem c10905 : check p10905 13237930238443008643 13 = true := check_combine (v := 47) (l := p10906) (r := p10915) (m := 13237930238443008643) (k := 13) (by decide +kernel) c10906 c10915

def p10887 : Plan := .step 17 p10888 p10905
theorem c10887 : check p10887 13237930238443139715 13 = true := check_combine (v := 17) (l := p10888) (r := p10905) (m := 13237930238443139715) (k := 13) (by decide +kernel) c10888 c10905

def p10865 : Plan := .step 6 p10866 p10887
theorem c10865 : check p10865 13237930238443139779 13 = true := check_combine (v := 6) (l := p10866) (r := p10887) (m := 13237930238443139779) (k := 13) (by decide +kernel) c10866 c10887

def p10847 : Plan := .step 48 p10848 p10865
theorem c10847 : check p10847 13238211713419850435 13 = true := check_combine (v := 48) (l := p10848) (r := p10865) (m := 13238211713419850435) (k := 13) (by decide +kernel) c10848 c10865

def p10815 : Plan := .step 21 p10816 p10847
theorem c10815 : check p10815 13238211713421947587 13 = true := check_combine (v := 21) (l := p10816) (r := p10847) (m := 13238211713421947587) (k := 13) (by decide +kernel) c10816 c10847

def p10761 : Plan := .step 14 p10762 p10815
theorem c10761 : check p10761 13238211713421963971 13 = true := check_combine (v := 14) (l := p10762) (r := p10815) (m := 13238211713421963971) (k := 13) (by decide +kernel) c10762 c10815

def p10735 : Plan := .step 45 p10736 p10761
theorem c10735 : check p10735 13238246897794052803 13 = true := check_combine (v := 45) (l := p10736) (r := p10761) (m := 13238246897794052803) (k := 13) (by decide +kernel) c10736 c10761

def p10697 : Plan := .step 5 p10698 p10735
theorem c10697 : check p10697 13238246897794052835 13 = true := check_combine (v := 5) (l := p10698) (r := p10735) (m := 13238246897794052835) (k := 13) (by decide +kernel) c10698 c10735

def p10651 : Plan := .step 42 p10652 p10697
theorem c10651 : check p10651 13238251295840563939 13 = true := check_combine (v := 42) (l := p10652) (r := p10697) (m := 13238251295840563939) (k := 13) (by decide +kernel) c10652 c10697

def p10617 : Plan := .step 59 p10618 p10651
theorem c10617 : check p10617 13814712048143987427 13 = true := check_combine (v := 59) (l := p10618) (r := p10651) (m := 13814712048143987427) (k := 13) (by decide +kernel) c10618 c10651

def p10579 : Plan := .step 54 p10580 p10617
theorem c10579 : check p10579 13832726446653469411 13 = true := check_combine (v := 54) (l := p10580) (r := p10617) (m := 13832726446653469411) (k := 13) (by decide +kernel) c10580 c10617

def p10521 : Plan := .step 32 p10522 p10579
theorem c10521 : check p10521 13832726450948436707 13 = true := check_combine (v := 32) (l := p10522) (r := p10579) (m := 13832726450948436707) (k := 13) (by decide +kernel) c10522 c10579

def p11034 : Plan := .step 59 p11035 p11046
theorem c11034 : check p11034 6876309298949419171 12 = true := check_combine (v := 59) (l := p11035) (r := p11046) (m := 6876309298949419171) (k := 12) (by decide +kernel) c11035 c11046

def p11094 : Plan := .step 60 p11095 p11110
theorem c11094 : check p11094 19923254979257725251 12 = true := check_combine (v := 60) (l := p11095) (r := p11110) (m := 19923254979257725251) (k := 12) (by decide +kernel) c11095 c11110

def p11090 : Plan := .step 27 p11091 p11094
theorem c11090 : check p11090 19923254979391942979 12 = true := check_combine (v := 27) (l := p11091) (r := p11094) (m := 19923254979391942979) (k := 12) (by decide +kernel) c11091 c11094

def p11178 : Plan := .step 7 p11179 p11188
theorem c11178 : check p11178 5128925058000515779 12 = true := check_combine (v := 7) (l := p11179) (r := p11188) (m := 5128925058000515779) (k := 12) (by decide +kernel) c11179 c11188

def p11413 : Plan := .step 48 p11414 p11431
theorem c11413 : check p11413 23595931687898842083 13 = true := check_combine (v := 48) (l := p11414) (r := p11431) (m := 23595931687898842083) (k := 13) (by decide +kernel) c11414 c11431

def p11395 : Plan := .step 37 p11396 p11413
theorem c11395 : check p11395 23595931825337795555 13 = true := check_combine (v := 37) (l := p11396) (r := p11413) (m := 23595931825337795555) (k := 13) (by decide +kernel) c11396 c11413

def p11377 : Plan := .step 51 p11378 p11395
theorem c11377 : check p11377 23598183625151480803 13 = true := check_combine (v := 51) (l := p11378) (r := p11395) (m := 23598183625151480803) (k := 13) (by decide +kernel) c11378 c11395

def p11361 : Plan := .step 14 p11362 p11377
theorem c11361 : check p11361 23598183625151497187 13 = true := check_combine (v := 14) (l := p11362) (r := p11377) (m := 23598183625151497187) (k := 13) (by decide +kernel) c11362 c11377

def p11337 : Plan := .step 43 p11338 p11361
theorem c11337 : check p11337 23598192421244519395 13 = true := check_combine (v := 43) (l := p11338) (r := p11361) (m := 23598192421244519395) (k := 13) (by decide +kernel) c11338 c11361

def p11311 : Plan := .step 21 p11312 p11337
theorem c11311 : check p11311 23598192421246616547 13 = true := check_combine (v := 21) (l := p11312) (r := p11337) (m := 23598192421246616547) (k := 13) (by decide +kernel) c11312 c11337

def p11269 : Plan := .step 13 p11270 p11311
theorem c11269 : check p11269 23598192421246624739 13 = true := check_combine (v := 13) (l := p11270) (r := p11311) (m := 23598192421246624739) (k := 13) (by decide +kernel) c11270 c11311

def p11231 : Plan := .step 12 p11232 p11269
theorem c11231 : check p11231 23598192421246628835 13 = true := check_combine (v := 12) (l := p11232) (r := p11269) (m := 23598192421246628835) (k := 13) (by decide +kernel) c11232 c11269

def p11177 : Plan := .step 27 p11178 p11231
theorem c11177 : check p11177 23598192421380846563 13 = true := check_combine (v := 27) (l := p11178) (r := p11231) (m := 23598192421380846563) (k := 13) (by decide +kernel) c11178 c11231

def p11149 : Plan := .step 60 p11150 p11177
theorem c11149 : check p11149 24751113925987693539 13 = true := check_combine (v := 60) (l := p11150) (r := p11177) (m := 24751113925987693539) (k := 13) (by decide +kernel) c11150 c11177

def p11089 : Plan := .step 59 p11090 p11149
theorem c11089 : check p11089 25327574678291117027 13 = true := check_combine (v := 59) (l := p11090) (r := p11149) (m := 25327574678291117027) (k := 13) (by decide +kernel) c11090 c11149

def p11033 : Plan := .step 40 p11034 p11089
theorem c11033 : check p11033 25327575777802744803 13 = true := check_combine (v := 40) (l := p11034) (r := p11089) (m := 25327575777802744803) (k := 13) (by decide +kernel) c11034 c11089

def p10993 : Plan := .step 25 p10994 p11033
theorem c10993 : check p10993 25327575777836299235 13 = true := check_combine (v := 25) (l := p10994) (r := p11033) (m := 25327575777836299235) (k := 13) (by decide +kernel) c10994 c11033

def p11548 : Plan := .step 40 p11549 p11558
theorem c11548 : check p11548 58866757272194019586 12 = true := check_combine (v := 40) (l := p11549) (r := p11558) (m := 58866757272194019586) (k := 12) (by decide +kernel) c11549 c11558

def p11546 : Plan := .step 27 p11547 p11548
theorem c11546 : check p11546 58866757272328237314 12 = true := check_combine (v := 27) (l := p11547) (r := p11548) (m := 58866757272328237314) (k := 12) (by decide +kernel) c11547 c11548

def p11717 : Plan := .step 37 p11718 p11727
theorem c11717 : check p11717 72917846418644022018 13 = true := check_combine (v := 37) (l := p11718) (r := p11727) (m := 72917846418644022018) (k := 13) (by decide +kernel) c11718 c11727

def p11705 : Plan := .step 27 p11706 p11717
theorem c11705 : check p11705 72917846418778239746 13 = true := check_combine (v := 27) (l := p11706) (r := p11717) (m := 72917846418778239746) (k := 13) (by decide +kernel) c11706 c11717

def p11675 : Plan := .step 7 p11676 p11705
theorem c11675 : check p11675 72917846418778239874 13 = true := check_combine (v := 7) (l := p11676) (r := p11705) (m := 72917846418778239874) (k := 13) (by decide +kernel) c11676 c11705

def p11655 : Plan := .step 47 p11656 p11675
theorem c11655 : check p11655 72917987156266595202 13 = true := check_combine (v := 47) (l := p11656) (r := p11675) (m := 72917987156266595202) (k := 13) (by decide +kernel) c11656 c11675

def p11637 : Plan := .step 14 p11638 p11655
theorem c11637 : check p11637 72917987156266611586 13 = true := check_combine (v := 14) (l := p11638) (r := p11655) (m := 72917987156266611586) (k := 13) (by decide +kernel) c11638 c11655

def p11617 : Plan := .step 5 p11618 p11637
theorem c11617 : check p11617 72917987156266611618 13 = true := check_combine (v := 5) (l := p11618) (r := p11637) (m := 72917987156266611618) (k := 13) (by decide +kernel) c11618 c11637

def p11597 : Plan := .step 40 p11598 p11617
theorem c11597 : check p11597 72917988255778239394 13 = true := check_combine (v := 40) (l := p11598) (r := p11617) (m := 72917988255778239394) (k := 13) (by decide +kernel) c11598 c11617

def p11545 : Plan := .step 59 p11546 p11597
theorem c11545 : check p11545 73494449008081662882 13 = true := check_combine (v := 59) (l := p11546) (r := p11597) (m := 73494449008081662882) (k := 13) (by decide +kernel) c11546 c11597

def p11521 : Plan := .step 25 p11522 p11545
theorem c11521 : check p11521 73494449008115217314 13 = true := check_combine (v := 25) (l := p11522) (r := p11545) (m := 73494449008115217314) (k := 13) (by decide +kernel) c11522 c11545

def p11475 : Plan := .step 6 p11476 p11521
theorem c11475 : check p11475 73494449008115217378 13 = true := check_combine (v := 6) (l := p11476) (r := p11521) (m := 73494449008115217378) (k := 13) (by decide +kernel) c11476 c11521

def p11947 : Plan := .step 17 p11948 p11955
theorem c11947 : check p11947 57717357504939569410 13 = true := check_combine (v := 17) (l := p11948) (r := p11955) (m := 57717357504939569410) (k := 13) (by decide +kernel) c11948 c11955

def p11939 : Plan := .step 14 p11940 p11947
theorem c11939 : check p11939 57717357504939585794 13 = true := check_combine (v := 14) (l := p11940) (r := p11947) (m := 57717357504939585794) (k := 13) (by decide +kernel) c11940 c11947

def p11917 : Plan := .step 0 p11918 p11939
theorem c11917 : check p11917 57717357504939585795 13 = true := check_combine (v := 0) (l := p11918) (r := p11939) (m := 57717357504939585795) (k := 13) (by decide +kernel) c11918 c11939

def p11909 : Plan := .step 26 p11910 p11917
theorem c11909 : check p11909 57717357505006694659 13 = true := check_combine (v := 26) (l := p11910) (r := p11917) (m := 57717357505006694659) (k := 13) (by decide +kernel) c11910 c11917

def p11899 : Plan := .step 22 p11900 p11909
theorem c11899 : check p11899 57717357505010888963 13 = true := check_combine (v := 22) (l := p11900) (r := p11909) (m := 57717357505010888963) (k := 13) (by decide +kernel) c11900 c11909

def p11889 : Plan := .step 20 p11890 p11899
theorem c11889 : check p11889 57717357505011937539 13 = true := check_combine (v := 20) (l := p11890) (r := p11899) (m := 57717357505011937539) (k := 13) (by decide +kernel) c11890 c11899

def p11879 : Plan := .step 47 p11880 p11889
theorem c11879 : check p11879 57717498242500292867 13 = true := check_combine (v := 47) (l := p11880) (r := p11889) (m := 57717498242500292867) (k := 13) (by decide +kernel) c11880 c11889

def p11863 : Plan := .step 40 p11864 p11879
theorem c11863 : check p11863 57717499342011920643 13 = true := check_combine (v := 40) (l := p11864) (r := p11879) (m := 57717499342011920643) (k := 13) (by decide +kernel) c11864 c11879

def p11845 : Plan := .step 27 p11846 p11863
theorem c11845 : check p11845 57717499342146138371 13 = true := check_combine (v := 27) (l := p11846) (r := p11863) (m := 57717499342146138371) (k := 13) (by decide +kernel) c11846 c11863

def p11831 : Plan := .step 60 p11832 p11845
theorem c11831 : check p11831 58870420846752985347 13 = true := check_combine (v := 60) (l := p11832) (r := p11845) (m := 58870420846752985347) (k := 13) (by decide +kernel) c11832 c11845

def p11801 : Plan := .step 25 p11802 p11831
theorem c11801 : check p11801 58870420846786539779 13 = true := check_combine (v := 25) (l := p11802) (r := p11831) (m := 58870420846786539779) (k := 13) (by decide +kernel) c11802 c11831

def p11771 : Plan := .step 6 p11772 p11801
theorem c11771 : check p11771 58870420846786539843 13 = true := check_combine (v := 6) (l := p11772) (r := p11801) (m := 58870420846786539843) (k := 13) (by decide +kernel) c11772 c11801

def p12038 : Plan := .step 9 p12039 p12052
theorem c12038 : check p12038 26757167907310551936 12 = true := check_combine (v := 9) (l := p12039) (r := p12052) (m := 26757167907310551936) (k := 12) (by decide +kernel) c12039 c12052

def p12182 : Plan := .step 21 p12183 p12190
theorem c12182 : check p12182 25598608005209391233 12 = true := check_combine (v := 21) (l := p12183) (r := p12190) (m := 25598608005209391233) (k := 12) (by decide +kernel) c12183 c12190

def p12168 : Plan := .step 13 p12169 p12182
theorem c12168 : check p12168 25598608005209399425 12 = true := check_combine (v := 13) (l := p12169) (r := p12182) (m := 25598608005209399425) (k := 12) (by decide +kernel) c12169 c12182

def p12337 : Plan := .step 19 p12338 p12355
theorem c12337 : check p12337 26757176603448980353 13 = true := check_combine (v := 19) (l := p12338) (r := p12355) (m := 26757176603448980353) (k := 13) (by decide +kernel) c12338 c12355

def p12307 : Plan := .step 17 p12308 p12337
theorem c12307 : check p12307 26757176603449111425 13 = true := check_combine (v := 17) (l := p12308) (r := p12337) (m := 26757176603449111425) (k := 13) (by decide +kernel) c12308 c12337

def p12297 : Plan := .step 27 p12298 p12307
theorem c12297 : check p12297 26757176603583329153 13 = true := check_combine (v := 27) (l := p12298) (r := p12307) (m := 26757176603583329153) (k := 13) (by decide +kernel) c12298 c12307

def p12267 : Plan := .step 26 p12268 p12297
theorem c12267 : check p12267 26757176603650438017 13 = true := check_combine (v := 26) (l := p12268) (r := p12297) (m := 26757176603650438017) (k := 13) (by decide +kernel) c12268 c12297

def p12237 : Plan := .step 25 p12238 p12267
theorem c12237 : check p12237 26757176603683992449 13 = true := check_combine (v := 25) (l := p12238) (r := p12267) (m := 26757176603683992449) (k := 13) (by decide +kernel) c12238 c12267

def p12167 : Plan := .step 14 p12168 p12237
theorem c12167 : check p12167 26757176603684008833 13 = true := check_combine (v := 14) (l := p12168) (r := p12237) (m := 26757176603684008833) (k := 13) (by decide +kernel) c12168 c12237

def p12139 : Plan := .step 43 p12140 p12167
theorem c12139 : check p12139 26757185399777031041 13 = true := check_combine (v := 43) (l := p12140) (r := p12167) (m := 26757185399777031041) (k := 13) (by decide +kernel) c12140 c12167

def p12099 : Plan := .step 37 p12100 p12139
theorem c12099 : check p12099 26757185537215984513 13 = true := check_combine (v := 37) (l := p12100) (r := p12139) (m := 26757185537215984513) (k := 13) (by decide +kernel) c12100 c12139

def p12037 : Plan := .step 5 p12038 p12099
theorem c12037 : check p12037 26757185537215984545 13 = true := check_combine (v := 5) (l := p12038) (r := p12099) (m := 26757185537215984545) (k := 13) (by decide +kernel) c12038 c12099

def p11997 : Plan := .step 48 p11998 p12037
theorem c11997 : check p11997 26757467012192695201 13 = true := check_combine (v := 48) (l := p11998) (r := p12037) (m := 26757467012192695201) (k := 13) (by decide +kernel) c11998 c12037

def p12623 : Plan := .step 14 p12624 p12629
theorem c12623 : check p12623 65972117284205776897 13 = true := check_combine (v := 14) (l := p12624) (r := p12629) (m := 65972117284205776897) (k := 13) (by decide +kernel) c12624 c12629

def p12615 : Plan := .step 62 p12616 p12623
theorem c12615 : check p12615 70583803302633164801 13 = true := check_combine (v := 62) (l := p12616) (r := p12623) (m := 70583803302633164801) (k := 13) (by decide +kernel) c12616 c12623

def p12605 : Plan := .step 38 p12606 p12615
theorem c12605 : check p12605 70583803577511071745 13 = true := check_combine (v := 38) (l := p12606) (r := p12615) (m := 70583803577511071745) (k := 13) (by decide +kernel) c12606 c12615

def p12589 : Plan := .step 7 p12590 p12605
theorem c12589 : check p12589 70583803577511071873 13 = true := check_combine (v := 7) (l := p12590) (r := p12605) (m := 70583803577511071873) (k := 13) (by decide +kernel) c12590 c12605

def p12575 : Plan := .step 5 p12576 p12589
theorem c12575 : check p12575 70583803577511071905 13 = true := check_combine (v := 5) (l := p12576) (r := p12589) (m := 70583803577511071905) (k := 13) (by decide +kernel) c12576 c12589

def p12553 : Plan := .step 61 p12554 p12575
theorem c12553 : check p12553 72889646586724765857 13 = true := check_combine (v := 61) (l := p12554) (r := p12575) (m := 72889646586724765857) (k := 13) (by decide +kernel) c12554 c12575

def p12525 : Plan := .step 32 p12526 p12553
theorem c12525 : check p12525 72889646591019733153 13 = true := check_combine (v := 32) (l := p12526) (r := p12553) (m := 72889646591019733153) (k := 13) (by decide +kernel) c12526 c12553

def p12503 : Plan := .step 54 p12504 p12525
theorem c12503 : check p12503 72907660989529215137 13 = true := check_combine (v := 54) (l := p12504) (r := p12525) (m := 72907660989529215137) (k := 13) (by decide +kernel) c12504 c12525

def p12473 : Plan := .step 42 p12474 p12503
theorem c12473 : check p12473 72907665387575726241 13 = true := check_combine (v := 42) (l := p12474) (r := p12503) (m := 72907665387575726241) (k := 13) (by decide +kernel) c12474 c12503

def p12449 : Plan := .step 35 p12450 p12473
theorem c12449 : check p12449 72907665421935464609 13 = true := check_combine (v := 35) (l := p12450) (r := p12473) (m := 72907665421935464609) (k := 13) (by decide +kernel) c12450 c12473

def p12417 : Plan := .step 13 p12418 p12449
theorem c12417 : check p12417 72907665421935472801 13 = true := check_combine (v := 13) (l := p12418) (r := p12449) (m := 72907665421935472801) (k := 13) (by decide +kernel) c12418 c12449

def p12399 : Plan := .step 53 p12400 p12417
theorem c12399 : check p12399 72916672621190213793 13 = true := check_combine (v := 53) (l := p12400) (r := p12417) (m := 72916672621190213793) (k := 13) (by decide +kernel) c12400 c12417

def p12825 : Plan := .step 14 p12826 p12835
theorem c12825 : check p12825 63559511392944013698 13 = true := check_combine (v := 14) (l := p12826) (r := p12835) (m := 63559511392944013698) (k := 13) (by decide +kernel) c12826 c12835

def p12811 : Plan := .step 0 p12812 p12825
theorem c12811 : check p12811 63559511392944013699 13 = true := check_combine (v := 0) (l := p12812) (r := p12825) (m := 63559511392944013699) (k := 13) (by decide +kernel) c12812 c12825

def p12797 : Plan := .step 13 p12798 p12811
theorem c12797 : check p12797 63559511392944021891 13 = true := check_combine (v := 13) (l := p12798) (r := p12811) (m := 63559511392944021891) (k := 13) (by decide +kernel) c12798 c12811

def p12777 : Plan := .step 12 p12778 p12797
theorem c12777 : check p12777 63559511392944025987 13 = true := check_combine (v := 12) (l := p12778) (r := p12797) (m := 63559511392944025987) (k := 13) (by decide +kernel) c12778 c12797

def p12755 : Plan := .step 40 p12756 p12777
theorem c12755 : check p12755 63559512492455653763 13 = true := check_combine (v := 40) (l := p12756) (r := p12777) (m := 63559512492455653763) (k := 13) (by decide +kernel) c12756 c12777

def p12733 : Plan := .step 26 p12734 p12755
theorem c12733 : check p12733 63559512492522762627 13 = true := check_combine (v := 26) (l := p12734) (r := p12755) (m := 63559512492522762627) (k := 13) (by decide +kernel) c12734 c12755

def p12705 : Plan := .step 5 p12706 p12733
theorem c12705 : check p12705 63559512492522762659 13 = true := check_combine (v := 5) (l := p12706) (r := p12733) (m := 63559512492522762659) (k := 13) (by decide +kernel) c12706 c12733

def p12673 : Plan := .step 50 p12674 p12705
theorem c12673 : check p12673 63560638392429605283 13 = true := check_combine (v := 50) (l := p12674) (r := p12705) (m := 63560638392429605283) (k := 13) (by decide +kernel) c12674 c12705

def p13053 : Plan := .step 29 p13054 p13063
theorem c13053 : check p13053 71703141051279872898 13 = true := check_combine (v := 29) (l := p13054) (r := p13063) (m := 71703141051279872898) (k := 13) (by decide +kernel) c13054 c13063

def p13037 : Plan := .step 20 p13038 p13053
theorem c13037 : check p13037 71703141051280921474 13 = true := check_combine (v := 20) (l := p13038) (r := p13053) (m := 71703141051280921474) (k := 13) (by decide +kernel) c13038 c13053

def p13017 : Plan := .step 26 p13018 p13037
theorem c13017 : check p13017 71703141051348030338 13 = true := check_combine (v := 26) (l := p13018) (r := p13037) (m := 71703141051348030338) (k := 13) (by decide +kernel) c13018 c13037

def p13005 : Plan := .step 17 p13006 p13017
theorem c13005 : check p13005 71703141051348161410 13 = true := check_combine (v := 17) (l := p13006) (r := p13017) (m := 71703141051348161410) (k := 13) (by decide +kernel) c13006 c13017

def p12973 : Plan := .step 0 p12974 p13005
theorem c12973 : check p12973 71703141051348161411 13 = true := check_combine (v := 0) (l := p12974) (r := p13005) (m := 71703141051348161411) (k := 13) (by decide +kernel) c12974 c13005

def p12949 : Plan := .step 40 p12950 p12973
theorem c12949 : check p12949 71703142150859789187 13 = true := check_combine (v := 40) (l := p12950) (r := p12973) (m := 71703142150859789187) (k := 13) (by decide +kernel) c12950 c12973

def p12919 : Plan := .step 13 p12920 p12949
theorem c12919 : check p12919 71703142150859797379 13 = true := check_combine (v := 13) (l := p12920) (r := p12949) (m := 71703142150859797379) (k := 13) (by decide +kernel) c12920 c12949

def p12875 : Plan := .step 5 p12876 p12919
theorem c12875 : check p12875 71703142150859797411 13 = true := check_combine (v := 5) (l := p12876) (r := p12919) (m := 71703142150859797411) (k := 13) (by decide +kernel) c12876 c12919

def p13227 : Plan := .step 42 p13228 p13243
theorem c13227 : check p13227 71713401763457155840 13 = true := check_combine (v := 42) (l := p13228) (r := p13243) (m := 71713401763457155840) (k := 13) (by decide +kernel) c13228 c13243

def p13217 : Plan := .step 40 p13218 p13227
theorem c13217 : check p13217 71713402862968783616 13 = true := check_combine (v := 40) (l := p13218) (r := p13227) (m := 71713402862968783616) (k := 13) (by decide +kernel) c13218 c13227

def p13197 : Plan := .step 26 p13198 p13217
theorem c13197 : check p13197 71713402863035892480 13 = true := check_combine (v := 26) (l := p13198) (r := p13217) (m := 71713402863035892480) (k := 13) (by decide +kernel) c13198 c13217

def p13177 : Plan := .step 17 p13178 p13197
theorem c13177 : check p13177 71713402863036023552 13 = true := check_combine (v := 17) (l := p13178) (r := p13197) (m := 71713402863036023552) (k := 13) (by decide +kernel) c13178 c13197

def p13167 : Plan := .step 50 p13168 p13177
theorem c13167 : check p13167 71714528762942866176 13 = true := check_combine (v := 50) (l := p13168) (r := p13177) (m := 71714528762942866176) (k := 13) (by decide +kernel) c13168 c13177

def p13145 : Plan := .step 47 p13146 p13167
theorem c13145 : check p13145 71714669500431221504 13 = true := check_combine (v := 47) (l := p13146) (r := p13167) (m := 71714669500431221504) (k := 13) (by decide +kernel) c13146 c13167

def p13109 : Plan := .step 7 p13110 p13145
theorem c13109 : check p13109 71714669500431221632 13 = true := check_combine (v := 7) (l := p13110) (r := p13145) (m := 71714669500431221632) (k := 13) (by decide +kernel) c13110 c13145

def p13443 : Plan := .step 17 p13444 p13449
theorem c13443 : check p13443 71701969072893346307 13 = true := check_combine (v := 17) (l := p13444) (r := p13449) (m := 71701969072893346307) (k := 13) (by decide +kernel) c13444 c13449

def p13427 : Plan := .step 12 p13428 p13443
theorem c13427 : check p13427 71701969072893350403 13 = true := check_combine (v := 12) (l := p13428) (r := p13443) (m := 71701969072893350403) (k := 13) (by decide +kernel) c13428 c13443

def p13391 : Plan := .step 8 p13392 p13427
theorem c13391 : check p13391 71701969072893350659 13 = true := check_combine (v := 8) (l := p13392) (r := p13427) (m := 71701969072893350659) (k := 13) (by decide +kernel) c13392 c13427

def p13367 : Plan := .step 50 p13368 p13391
theorem c13367 : check p13367 71703094972800193283 13 = true := check_combine (v := 50) (l := p13368) (r := p13391) (m := 71703094972800193283) (k := 13) (by decide +kernel) c13368 c13391

def p13347 : Plan := .step 42 p13348 p13367
theorem c13347 : check p13347 71703099370846704387 13 = true := check_combine (v := 42) (l := p13348) (r := p13367) (m := 71703099370846704387) (k := 13) (by decide +kernel) c13348 c13367

def p13323 : Plan := .step 40 p13324 p13347
theorem c13323 : check p13323 71703100470358332163 13 = true := check_combine (v := 40) (l := p13324) (r := p13347) (m := 71703100470358332163) (k := 13) (by decide +kernel) c13324 c13347

def p13287 : Plan := .step 13 p13288 p13323
theorem c13287 : check p13287 71703100470358340355 13 = true := check_combine (v := 13) (l := p13288) (r := p13323) (m := 71703100470358340355) (k := 13) (by decide +kernel) c13288 c13323

def p13607 : Plan := .step 19 p13608 p13627
theorem c13607 : check p13607 50983328204591087618 13 = true := check_combine (v := 19) (l := p13608) (r := p13627) (m := 50983328204591087618) (k := 13) (by decide +kernel) c13608 c13627

def p13603 : Plan := .step 47 p13604 p13607
theorem c13603 : check p13603 50983468942079442946 13 = true := check_combine (v := 47) (l := p13604) (r := p13607) (m := 50983468942079442946) (k := 13) (by decide +kernel) c13604 c13607

def p13597 : Plan := .step 20 p13598 p13603
theorem c13597 : check p13597 50983468942080491522 13 = true := check_combine (v := 20) (l := p13598) (r := p13603) (m := 50983468942080491522) (k := 13) (by decide +kernel) c13598 c13603

def p13583 : Plan := .step 0 p13584 p13597
theorem c13583 : check p13583 50983468942080491523 13 = true := check_combine (v := 0) (l := p13584) (r := p13597) (m := 50983468942080491523) (k := 13) (by decide +kernel) c13584 c13597

def p13579 : Plan := .step 53 p13580 p13583
theorem c13579 : check p13579 50992476141335232515 13 = true := check_combine (v := 53) (l := p13580) (r := p13583) (m := 50992476141335232515) (k := 13) (by decide +kernel) c13580 c13583

def p13547 : Plan := .step 50 p13548 p13579
theorem c13547 : check p13547 50993602041242075139 13 = true := check_combine (v := 50) (l := p13548) (r := p13579) (m := 50993602041242075139) (k := 13) (by decide +kernel) c13548 c13579

def p13527 : Plan := .step 42 p13528 p13547
theorem c13527 : check p13527 50993606439288586243 13 = true := check_combine (v := 42) (l := p13528) (r := p13547) (m := 50993606439288586243) (k := 13) (by decide +kernel) c13528 c13547

def p13511 : Plan := .step 13 p13512 p13527
theorem c13511 : check p13511 50993606439288594435 13 = true := check_combine (v := 13) (l := p13512) (r := p13527) (m := 50993606439288594435) (k := 13) (by decide +kernel) c13512 c13527

def p13493 : Plan := .step 12 p13494 p13511
theorem c13493 : check p13493 50993606439288598531 13 = true := check_combine (v := 12) (l := p13494) (r := p13511) (m := 50993606439288598531) (k := 13) (by decide +kernel) c13494 c13511

def p13715 : Plan := .step 17 p13716 p13733
theorem c13715 : check p13715 4833838876677776131 13 = true := check_combine (v := 17) (l := p13716) (r := p13733) (m := 4833838876677776131) (k := 13) (by decide +kernel) c13716 c13733

def p13707 : Plan := .step 14 p13708 p13715
theorem c13707 : check p13707 4833838876677792515 13 = true := check_combine (v := 14) (l := p13708) (r := p13715) (m := 4833838876677792515) (k := 13) (by decide +kernel) c13708 c13715

def p13693 : Plan := .step 37 p13694 p13707
theorem c13693 : check p13693 4833839014116745987 13 = true := check_combine (v := 37) (l := p13694) (r := p13707) (m := 4833839014116745987) (k := 13) (by decide +kernel) c13694 c13707

def p13675 : Plan := .step 26 p13676 p13693
theorem c13675 : check p13675 4833839014183854851 13 = true := check_combine (v := 26) (l := p13676) (r := p13693) (m := 4833839014183854851) (k := 13) (by decide +kernel) c13676 c13693

def p13663 : Plan := .step 61 p13664 p13675
theorem c13663 : check p13663 7139682023397548803 13 = true := check_combine (v := 61) (l := p13664) (r := p13675) (m := 7139682023397548803) (k := 13) (by decide +kernel) c13664 c13675

def p13789 : Plan := .step 26 p13790 p13809
theorem c13789 : check p13789 18715023686774821635 13 = true := check_combine (v := 26) (l := p13790) (r := p13809) (m := 18715023686774821635) (k := 13) (by decide +kernel) c13790 c13809

def p13779 : Plan := .step 17 p13780 p13789
theorem c13779 : check p13779 18715023686774952707 13 = true := check_combine (v := 17) (l := p13780) (r := p13789) (m := 18715023686774952707) (k := 13) (by decide +kernel) c13780 c13789

def p13767 : Plan := .step 13 p13768 p13779
theorem c13767 : check p13767 18715023686774960899 13 = true := check_combine (v := 13) (l := p13768) (r := p13779) (m := 18715023686774960899) (k := 13) (by decide +kernel) c13768 c13779

def p13863 : Plan := .step 42 p13864 p13873
theorem c13863 : check p13863 34849204496661107459 13 = true := check_combine (v := 42) (l := p13864) (r := p13873) (m := 34849204496661107459) (k := 13) (by decide +kernel) c13864 c13873

def p13853 : Plan := .step 29 p13854 p13863
theorem c13853 : check p13853 34849204497197978371 13 = true := check_combine (v := 29) (l := p13854) (r := p13863) (m := 34849204497197978371) (k := 13) (by decide +kernel) c13854 c13863

def p13937 : Plan := .step 14 p13938 p13947
theorem c13937 : check p13937 18642961664432820483 13 = true := check_combine (v := 14) (l := p13938) (r := p13947) (m := 18642961664432820483) (k := 13) (by decide +kernel) c13938 c13947

def p13919 : Plan := .step 26 p13920 p13937
theorem c13919 : check p13919 18642961664499929347 13 = true := check_combine (v := 26) (l := p13920) (r := p13937) (m := 18642961664499929347) (k := 13) (by decide +kernel) c13920 c13937

def p14011 : Plan := .step 43 p14012 p14017
theorem c14011 : check p14011 53217130567709774082 13 = true := check_combine (v := 43) (l := p14012) (r := p14017) (m := 53217130567709774082) (k := 13) (by decide +kernel) c14012 c14017

def p14003 : Plan := .step 20 p14004 p14011
theorem c14003 : check p14003 53217130567710822658 13 = true := check_combine (v := 20) (l := p14004) (r := p14011) (m := 53217130567710822658) (k := 13) (by decide +kernel) c14004 c14011

def p13993 : Plan := .step 0 p13994 p14003
theorem c13993 : check p13993 53217130567710822659 13 = true := check_combine (v := 0) (l := p13994) (r := p14003) (m := 53217130567710822659) (k := 13) (by decide +kernel) c13994 c14003

def p14063 : Plan := .step 8 p14064 p14077
theorem c14063 : check p14063 60031024781129700099 13 = true := check_combine (v := 8) (l := p14064) (r := p14077) (m := 60031024781129700099) (k := 13) (by decide +kernel) c14064 c14077

def p14139 : Plan := .step 1 p14140 p14161
theorem c14139 : check p14139 48537881896150647298 13 = true := check_combine (v := 1) (l := p14140) (r := p14161) (m := 48537881896150647298) (k := 13) (by decide +kernel) c14140 c14161

def p14129 : Plan := .step 12 p14130 p14139
theorem c14129 : check p14129 48537881896150651394 13 = true := check_combine (v := 12) (l := p14130) (r := p14139) (m := 48537881896150651394) (k := 13) (by decide +kernel) c14130 c14139

def p14119 : Plan := .step 0 p14120 p14129
theorem c14119 : check p14119 48537881896150651395 13 = true := check_combine (v := 0) (l := p14120) (r := p14129) (m := 48537881896150651395) (k := 13) (by decide +kernel) c14120 c14129

def p14370 : Plan := .step 37 p14371 p14378
theorem c14370 : check p14370 64831905966850835202 14 = true := check_combine (v := 37) (l := p14371) (r := p14378) (m := 64831905966850835202) (k := 14) (by decide +kernel) c14371 c14378

def p14362 : Plan := .step 61 p14363 p14370
theorem c14362 : check p14362 67137748976064529154 14 = true := check_combine (v := 61) (l := p14363) (r := p14370) (m := 67137748976064529154) (k := 14) (by decide +kernel) c14363 c14370

def p14356 : Plan := .step 30 p14357 p14362
theorem c14356 : check p14356 67137748977138270978 14 = true := check_combine (v := 30) (l := p14357) (r := p14362) (m := 67137748977138270978) (k := 14) (by decide +kernel) c14357 c14362

def p14350 : Plan := .step 62 p14351 p14356
theorem c14350 : check p14350 71749434995565658882 14 = true := check_combine (v := 62) (l := p14351) (r := p14356) (m := 71749434995565658882) (k := 14) (by decide +kernel) c14351 c14356

def p14334 : Plan := .step 29 p14335 p14350
theorem c14334 : check p14334 71749434996102529794 14 = true := check_combine (v := 29) (l := p14335) (r := p14350) (m := 71749434996102529794) (k := 14) (by decide +kernel) c14335 c14350

def p14324 : Plan := .step 27 p14325 p14334
theorem c14324 : check p14324 71749434996236747522 14 = true := check_combine (v := 27) (l := p14325) (r := p14334) (m := 71749434996236747522) (k := 14) (by decide +kernel) c14325 c14334

def p14298 : Plan := .step 22 p14299 p14324
theorem c14298 : check p14298 71749434996240941826 14 = true := check_combine (v := 22) (l := p14299) (r := p14324) (m := 71749434996240941826) (k := 14) (by decide +kernel) c14299 c14324

def p14282 : Plan := .step 14 p14283 p14298
theorem c14282 : check p14282 71749434996240958210 14 = true := check_combine (v := 14) (l := p14283) (r := p14298) (m := 71749434996240958210) (k := 14) (by decide +kernel) c14283 c14298

def p14256 : Plan := .step 43 p14257 p14282
theorem c14256 : check p14256 71749443792333980418 14 = true := check_combine (v := 43) (l := p14257) (r := p14282) (m := 71749443792333980418) (k := 14) (by decide +kernel) c14257 c14282

def p14222 : Plan := .step 12 p14223 p14256
theorem c14222 : check p14222 71749443792333984514 14 = true := check_combine (v := 12) (l := p14223) (r := p14256) (m := 71749443792333984514) (k := 14) (by decide +kernel) c14223 c14256

def p14196 : Plan := .step 0 p14197 p14222
theorem c14196 : check p14196 71749443792333984515 14 = true := check_combine (v := 0) (l := p14197) (r := p14222) (m := 71749443792333984515) (k := 14) (by decide +kernel) c14197 c14222

def p14118 : Plan := .step 26 p14119 p14196
theorem c14118 : check p14118 71749443792401093379 14 = true := check_combine (v := 26) (l := p14119) (r := p14196) (m := 71749443792401093379) (k := 14) (by decide +kernel) c14119 c14196

def p14062 : Plan := .step 20 p14063 p14118
theorem c14062 : check p14062 71749443792402141955 14 = true := check_combine (v := 20) (l := p14063) (r := p14118) (m := 71749443792402141955) (k := 14) (by decide +kernel) c14063 c14118

def p13992 : Plan := .step 17 p13993 p14062
theorem c13992 : check p13992 71749443792402273027 14 = true := check_combine (v := 17) (l := p13993) (r := p14062) (m := 71749443792402273027) (k := 14) (by decide +kernel) c13993 c14062

def p13918 : Plan := .step 42 p13919 p13992
theorem c13918 : check p13918 71749448190448784131 14 = true := check_combine (v := 42) (l := p13919) (r := p13992) (m := 71749448190448784131) (k := 14) (by decide +kernel) c13919 c13992

def p13852 : Plan := .step 13 p13853 p13918
theorem c13852 : check p13852 71749448190448792323 14 = true := check_combine (v := 13) (l := p13853) (r := p13918) (m := 71749448190448792323) (k := 14) (by decide +kernel) c13853 c13918

def p13766 : Plan := .step 50 p13767 p13852
theorem c13766 : check p13766 71750574090355634947 14 = true := check_combine (v := 50) (l := p13767) (r := p13852) (m := 71750574090355634947) (k := 14) (by decide +kernel) c13767 c13852

def p13662 : Plan := .step 47 p13663 p13766
theorem c13662 : check p13662 71750714827843990275 14 = true := check_combine (v := 47) (l := p13663) (r := p13766) (m := 71750714827843990275) (k := 14) (by decide +kernel) c13663 c13766

def p13492 : Plan := .step 40 p13493 p13662
theorem c13492 : check p13492 71750715927355618051 14 = true := check_combine (v := 40) (l := p13493) (r := p13662) (m := 71750715927355618051) (k := 14) (by decide +kernel) c13493 c13662

def p13286 : Plan := .step 7 p13287 p13492
theorem c13286 : check p13286 71750715927355618179 14 = true := check_combine (v := 7) (l := p13287) (r := p13492) (m := 71750715927355618179) (k := 14) (by decide +kernel) c13287 c13492

def p13108 : Plan := .step 5 p13109 p13286
theorem c13108 : check p13108 71750715927355618211 14 = true := check_combine (v := 5) (l := p13109) (r := p13286) (m := 71750715927355618211) (k := 14) (by decide +kernel) c13109 c13286

def p12874 : Plan := .step 60 p12875 p13108
theorem c12874 : check p12874 72903637431962465187 14 = true := check_combine (v := 60) (l := p12875) (r := p13108) (m := 72903637431962465187) (k := 14) (by decide +kernel) c12875 c13108

def p12672 : Plan := .step 54 p12673 p12874
theorem c12672 : check p12672 72921651830471947171 14 = true := check_combine (v := 54) (l := p12673) (r := p12874) (m := 72921651830471947171) (k := 14) (by decide +kernel) c12673 c12874

def p12398 : Plan := .step 25 p12399 p12672
theorem c12398 : check p12398 72921651830505501603 14 = true := check_combine (v := 25) (l := p12399) (r := p12672) (m := 72921651830505501603) (k := 14) (by decide +kernel) c12399 c12672

def p11996 : Plan := .step 6 p11997 p12398
theorem c11996 : check p11996 72921651830505501667 14 = true := check_combine (v := 6) (l := p11997) (r := p12398) (m := 72921651830505501667) (k := 14) (by decide +kernel) c11997 c12398

def p11770 : Plan := .step 59 p11771 p11996
theorem c11770 : check p11770 73498112582808925155 14 = true := check_combine (v := 59) (l := p11771) (r := p11996) (m := 73498112582808925155) (k := 14) (by decide +kernel) c11771 c11996

def p11474 : Plan := .step 58 p11475 p11770
theorem c11474 : check p11474 73786342958960636899 14 = true := check_combine (v := 58) (l := p11475) (r := p11770) (m := 73786342958960636899) (k := 14) (by decide +kernel) c11475 c11770

def p10992 : Plan := .step 49 p10993 p11474
theorem c10992 : check p10992 73786905908914058211 14 = true := check_combine (v := 49) (l := p10993) (r := p11474) (m := 73786905908914058211) (k := 14) (by decide +kernel) c10993 c11474

def p10520 : Plan := .step 46 p10521 p10992
theorem c10520 : check p10520 73786976277658235875 14 = true := check_combine (v := 46) (l := p10521) (r := p10992) (m := 73786976277658235875) (k := 14) (by decide +kernel) c10521 c10992

def p9922 : Plan := .step 34 p9923 p10520
theorem c9922 : check p9922 73786976294838105059 14 = true := check_combine (v := 34) (l := p9923) (r := p10520) (m := 73786976294838105059) (k := 14) (by decide +kernel) c9923 c10520

def p9132 : Plan := .step 16 p9133 p9922
theorem c9132 : check p9132 73786976294838170595 14 = true := check_combine (v := 16) (l := p9133) (r := p9922) (m := 73786976294838170595) (k := 14) (by decide +kernel) c9133 c9922

def p8262 : Plan := .step 15 p8263 p9132
theorem c8262 : check p8262 73786976294838203363 14 = true := check_combine (v := 15) (l := p8263) (r := p9132) (m := 73786976294838203363) (k := 14) (by decide +kernel) c8263 c9132

def p7088 : Plan := .step 11 p7089 p8262
theorem c7088 : check p7088 73786976294838205411 14 = true := check_combine (v := 11) (l := p7089) (r := p8262) (m := 73786976294838205411) (k := 14) (by decide +kernel) c7089 c8262

def p5808 : Plan := .step 10 p5809 p7088
theorem c5808 : check p5808 73786976294838206435 14 = true := check_combine (v := 10) (l := p5809) (r := p7088) (m := 73786976294838206435) (k := 14) (by decide +kernel) c5809 c7088

def p4426 : Plan := .step 4 p4427 p5808
theorem c4426 : check p4426 73786976294838206451 14 = true := check_combine (v := 4) (l := p4427) (r := p5808) (m := 73786976294838206451) (k := 14) (by decide +kernel) c4427 c5808

def p2460 : Plan := .step 3 p2461 p4426
theorem c2460 : check p2460 73786976294838206459 14 = true := check_combine (v := 3) (l := p2461) (r := p4426) (m := 73786976294838206459) (k := 14) (by decide +kernel) c2461 c4426

def p0 : Plan := .step 2 p1 p2460
theorem c0 : check p0 73786976294838206463 14 = true := check_combine (v := 2) (l := p1) (r := p2460) (m := 73786976294838206463) (k := 14) (by decide +kernel) c1 c2460
end Erdos151Ramsey.Archive66
