import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0621 : checkSingleBlackFast (6, -7) 12011 .east (0, -6) (-17, -18) = true := by
  decide +kernel

end LangtonsAnt
