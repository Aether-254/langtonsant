import FastCell

namespace LangtonsAnt

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem sbCell0114 : checkSingleBlackFast (-4, 0) 6531 .west (-6, 0) (-19, -16) = true := by
  decide +kernel

end LangtonsAnt
