import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0314 : checkSingleBlackFast (1, 11) 7915 .east (-1, -12) (-19, -11) = true := by
  decide +kernel

end LangtonsAnt
