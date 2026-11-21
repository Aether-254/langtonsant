import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0283 : checkSingleBlackFast (16, 11) 7127 .west (-4, -2) (-19, -4) = true := by
  decide +kernel

end LangtonsAnt
