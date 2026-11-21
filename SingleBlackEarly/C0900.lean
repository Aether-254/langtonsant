import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0900 : checkSingleBlackFast (-10, 12) 23116 .south (-7, -2) (-31, -10) = true := by
  decide +kernel

end LangtonsAnt
