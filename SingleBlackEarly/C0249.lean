import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0249 : checkSingleBlackFast (13, 6) 20209 .east (4, -10) (-18, -23) = true := by
  decide +kernel

end LangtonsAnt
