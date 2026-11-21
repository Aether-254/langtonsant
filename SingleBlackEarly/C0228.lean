import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0228 : checkSingleBlackFast (7, 9) 4923 .east (1, -11) (-18, -13) = true := by
  decide +kernel

end LangtonsAnt
