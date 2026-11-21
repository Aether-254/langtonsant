import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0897 : checkSingleBlackFast (-9, 11) 7375 .east (-1, -4) (-19, -19) = true := by
  decide +kernel

end LangtonsAnt
