import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0930 : checkSingleBlackFast (-13, 13) 8531 .east (-1, -6) (-21, -19) = true := by
  decide +kernel

end LangtonsAnt
