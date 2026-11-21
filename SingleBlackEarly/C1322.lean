import FastCell2

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell1322 : checkSingleBlackFast2 (-13, 15) 16561 .east (4, -13) (-33, -27) = true := by
  decide +kernel

end LangtonsAnt
