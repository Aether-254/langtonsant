import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1406 : checkSingleBlackFast (-19, 3) 19272 .south (-7, -1) (-31, -11) = true := by
  decide +kernel

end LangtonsAnt
