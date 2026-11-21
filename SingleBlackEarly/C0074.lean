import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0074 : checkSingleBlackFast (2, -5) 2169 .west (2, 5) (-13, -3) = true := by
  decide +kernel

end LangtonsAnt
